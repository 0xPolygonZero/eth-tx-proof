use std::collections::{BTreeMap, HashMap};
use std::sync::Arc;

use ethers::prelude::*;
use ethers::utils::rlp;
use evm_arithmetization::generation::mpt::AccountRlp;
use mpt_trie::nibbles::{Nibbles, NibblesIntern};
use mpt_trie::partial_trie::PartialTrie;
use mpt_trie::partial_trie::{HashedPartialTrie, Node};
use mpt_trie::trie_subsets::create_trie_subset;

use crate::utils::keccak;
use crate::EMPTY_HASH;

#[derive(Clone, Debug)]
pub struct MptNode(Vec<u8>);

#[derive(Default)]
pub struct Mpt {
    pub mpt: HashMap<H256, MptNode>,
    pub root: H256,
}

const EMPTY_TRIE_HASH: H256 = H256([
    86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153,
    108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
]);

impl Mpt {
    pub fn new() -> Self {
        Self {
            mpt: HashMap::new(),
            root: H256::zero(),
        }
    }

    pub fn to_partial_trie(&self) -> HashedPartialTrie {
        let trie = self.to_partial_trie_helper(self.root);
        if trie == Node::Hash(EMPTY_TRIE_HASH).into() {
            Node::Empty.into()
        } else {
            trie
        }
    }

    fn to_partial_trie_helper(&self, root: H256) -> HashedPartialTrie {
        let node = self.mpt.get(&root);
        let data = if let Some(mpt_node) = node {
            mpt_node.0.clone()
        } else {
            return Node::Hash(root).into();
        };
        let a = rlp::decode_list::<Vec<u8>>(&data);
        match a.len() {
            17 => {
                let value = a[16].clone();
                let mut children = vec![];
                for i in 0..16 {
                    if a[i].is_empty() {
                        children.push(Node::Empty.into());
                        continue;
                    }
                    children.push(Arc::new(Box::new(
                        self.to_partial_trie_helper(H256::from_slice(&a[i])),
                    )));
                }
                Node::Branch {
                    value,
                    children: children.try_into().unwrap(),
                }
                .into()
            }
            2 => match a[0][0] >> 4 {
                0 => {
                    let ext_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
                    Node::Extension {
                        nibbles: ext_prefix,
                        child: Arc::new(Box::new(
                            self.to_partial_trie_helper(H256::from_slice(&a[1])),
                        )),
                    }
                    .into()
                }
                1 => {
                    let b = a[0][0] & 0xf;
                    let mut ext_prefix = if a[0].len() > 1 {
                        Nibbles::from_bytes_be(&a[0][1..]).unwrap()
                    } else {
                        Nibbles {
                            count: 0,
                            packed: NibblesIntern::zero(),
                        }
                    };
                    ext_prefix.push_nibble_front(b);
                    Node::Extension {
                        nibbles: ext_prefix,
                        child: Arc::new(Box::new(
                            self.to_partial_trie_helper(H256::from_slice(&a[1])),
                        )),
                    }
                    .into()
                }
                2 => {
                    let leaf_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
                    Node::Leaf {
                        nibbles: leaf_prefix,
                        value: a[1].clone(),
                    }
                    .into()
                }
                3 => {
                    let b = a[0][0] & 0xf;
                    let mut leaf_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
                    leaf_prefix.push_nibble_front(b);
                    Node::Leaf {
                        nibbles: leaf_prefix,
                        value: a[1].clone(),
                    }
                    .into()
                }
                _ => panic!("wtf?"),
            },
            _ => panic!("wtf?"),
        }
    }
}

pub fn insert_mpt(mpt: &mut Mpt, proof: Vec<Bytes>) {
    for p in proof.into_iter() {
        // mpt.mpt.insert(H256(keccak256(&p)), MptNode(p.to_vec()));
        insert_mpt_helper(mpt, p);
    }
}

fn insert_mpt_helper(mpt: &mut Mpt, rlp_node: Bytes) {
    mpt.mpt
        .insert(H256(keccak(&rlp_node)), MptNode(rlp_node.to_vec()));
    let a = rlp::decode_list::<Vec<u8>>(&rlp_node);
    if a.len() == 2 {
        let prefix = a[0].clone();
        let is_leaf = (prefix[0] >> 4 == 2) || (prefix[0] >> 4 == 3);
        let mut nibbles = nibbles_from_hex_prefix_encoding(&prefix);
        loop {
            let node = rlp::encode_list::<Vec<u8>, _>(&[
                nibbles.to_hex_prefix_encoding(is_leaf).to_vec(),
                a[1].clone(),
            ]);
            mpt.mpt.insert(H256(keccak(&node)), MptNode(node.to_vec()));
            if nibbles.is_empty() {
                break;
            }
            nibbles.pop_next_nibble_front();
        }
    }
}

fn nibbles_from_hex_prefix_encoding(b: &[u8]) -> Nibbles {
    let mut b = b.to_vec();
    match b[0] >> 4 {
        0 | 2 => Nibbles::from_bytes_be(&b[1..]).unwrap(),
        1 | 3 => {
            b[0] &= 0xf;
            let mut bs = [0; 64];
            bs[64 - b.len()..].copy_from_slice(&b);
            Nibbles {
                count: 2 * b.len() - 1,
                // packed: U512::from_bytes_be(&bs).unwrap(),
                packed: NibblesIntern::from_big_endian(&b),
            }
            // Nibbles::from_bytes_be(&b).unwrap()
        }
        _ => panic!("wtf?"),
    }
}

pub fn apply_diffs(
    mut mpt: HashedPartialTrie,
    mut storage: HashMap<H256, HashedPartialTrie>,
    contract_code: &mut HashMap<H256, Vec<u8>>,
    trace: GethTrace,
) -> (HashedPartialTrie, HashMap<H256, HashedPartialTrie>) {
    let diff = if let GethTrace::Known(GethTraceFrame::PreStateTracer(PreStateFrame::Diff(diff))) =
        trace
    {
        diff
    } else {
        panic!("wtf?");
    };

    let empty_node = HashedPartialTrie::from(Node::Empty);

    let tokk = |k: H256| Nibbles::from_bytes_be(&keccak(k.0)).unwrap();

    for (addr, old) in &diff.pre {
        let key = H256(keccak(addr.0));
        if !diff.post.contains_key(addr) {
            storage.remove(&key);
        } else {
            let new = diff.post.get(addr).unwrap();
            if old.storage.clone().unwrap_or_default().is_empty()
                && new.storage.clone().unwrap_or_default().is_empty()
            {
                continue;
            }
            let mut trie = storage.get(&key).unwrap().clone();
            for (&k, &v) in &old.storage.clone().unwrap_or_default() {
                if !new.storage.clone().unwrap_or_default().contains_key(&k) {
                    // dbg!(format!("Del {:?} {:?}", addr, k));
                    trie.delete(tokk(k)).unwrap();
                    // println!("Done Del {:?} {:?}", addr, k);
                } else {
                    let sanity = trie.get(tokk(k)).unwrap();
                    let sanity = rlp::decode::<U256>(sanity).unwrap();
                    assert_eq!(sanity, v.into_uint());
                    let w = *new.storage.clone().unwrap_or_default().get(&k).unwrap();
                    trie.insert(tokk(k), rlp::encode(&w.into_uint()).to_vec())
                        .unwrap();
                }
            }
            for (&k, v) in &new.storage.clone().unwrap_or_default() {
                if !old.storage.clone().unwrap_or_default().contains_key(&k) {
                    trie.insert(tokk(k), rlp::encode(&v.into_uint()).to_vec())
                        .unwrap();
                }
            }
            storage.insert(key, trie);
        }
    }

    for (addr, new) in &diff.post {
        let key = H256(keccak(addr.0));
        if !diff.pre.contains_key(addr) {
            let mut trie = HashedPartialTrie::from(Node::Empty);
            for (&k, v) in &new.storage.clone().unwrap_or_default() {
                trie.insert(tokk(k), rlp::encode(&v.into_uint()).to_vec())
                    .unwrap();
            }
            storage.insert(key, trie);
        }
    }

    let tok = |addr: &Address| Nibbles::from_bytes_be(&keccak(addr.0)).unwrap();

    // Delete accounts that are not in the post state.
    for addr in diff.pre.keys() {
        if !diff.post.contains_key(addr) {
            mpt.delete(tok(addr)).unwrap();
        }
    }

    for (addr, acc) in &diff.post {
        if !diff.pre.contains_key(addr) {
            // New account
            let code_hash = acc
                .code
                .clone()
                .map(|s| {
                    if s.is_empty() {
                        EMPTY_HASH
                    } else {
                        let code = s.split_at(2).1;
                        let bytes = hex::decode(code).unwrap();
                        let h = H256(keccak(&bytes));
                        contract_code.insert(h, bytes);
                        h
                    }
                })
                .unwrap_or(EMPTY_HASH);
            let account = AccountRlp {
                nonce: acc.nonce.unwrap_or(U256::zero()),
                balance: acc.balance.unwrap_or(U256::zero()),
                storage_root: storage
                    .get(&H256(keccak(addr.0)))
                    .unwrap_or(&empty_node.clone())
                    .hash(),
                code_hash,
            };
            mpt.insert(tok(addr), rlp::encode(&account).to_vec())
                .unwrap();
        } else {
            let old = mpt
                .get(tok(addr))
                .map(|d| rlp::decode(d).unwrap())
                .unwrap_or(AccountRlp {
                    nonce: U256::zero(),
                    balance: U256::zero(),
                    storage_root: empty_node.hash(),
                    code_hash: EMPTY_HASH,
                });
            let code_hash = acc
                .code
                .clone()
                .map(|s| {
                    if s.is_empty() {
                        EMPTY_HASH
                    } else {
                        let code = s.split_at(2).1;
                        let bytes = hex::decode(code).unwrap();
                        let h = H256(keccak(&bytes));
                        contract_code.insert(h, bytes);
                        h
                    }
                })
                .unwrap_or(old.code_hash);
            let account = AccountRlp {
                nonce: acc.nonce.unwrap_or(old.nonce),
                balance: acc.balance.unwrap_or(old.balance),
                storage_root: storage
                    .get(&H256(keccak(addr.0)))
                    .map(|trie| trie.hash())
                    .unwrap_or(old.storage_root),
                code_hash,
            };
            mpt.insert(tok(addr), rlp::encode(&account).to_vec())
                .unwrap();
        }
    }

    (mpt, storage)
}

pub fn trim(
    trie: HashedPartialTrie,
    mut storage_mpts: HashMap<H256, HashedPartialTrie>,
    touched: BTreeMap<Address, AccountState>,
    has_storage_deletion: bool,
) -> (HashedPartialTrie, HashMap<H256, HashedPartialTrie>) {
    let tok = |addr: &Address| Nibbles::from_bytes_be(&keccak(addr.0)).unwrap();
    let keys = touched.keys().map(tok).collect::<Vec<_>>();
    let new_state_trie = create_trie_subset(&trie, keys).unwrap();
    if has_storage_deletion {
        // TODO: This is inefficient. Replace with a smarter solution.
        return (new_state_trie, storage_mpts);
    }
    let keys_to_addrs = touched
        .keys()
        .map(|addr| (H256(keccak(addr.0)), *addr))
        .collect::<HashMap<_, _>>();
    for (k, t) in storage_mpts.iter_mut() {
        if !keys_to_addrs.contains_key(k) {
            *t = HashedPartialTrie::from(Node::Hash(t.hash()));
        } else {
            let addr = keys_to_addrs.get(k).unwrap();
            let acc = touched.get(addr).unwrap();
            let keys = acc
                .storage
                .clone()
                .unwrap_or_default()
                .keys()
                .map(|slot| Nibbles::from_bytes_be(&keccak(slot.0)).unwrap())
                .collect::<Vec<_>>();

            if let Ok(trie) = create_trie_subset(t, keys) {
                *t = trie;
            }
        }
    }
    (new_state_trie, storage_mpts)
}
