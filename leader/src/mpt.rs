use std::{
    collections::{BTreeMap, HashMap},
    sync::Arc,
};

use alloy::{
    primitives::{Address, Bytes, FixedBytes, B256, U256},
    rlp::Decodable,
    rpc::types::trace::geth::{AccountState, GethTrace, PreStateFrame},
};
use evm_arithmetization::generation::mpt::AccountRlp;
use mpt_trie::{
    nibbles::{Nibbles, NibblesIntern},
    partial_trie::{HashedPartialTrie, Node, PartialTrie},
    trie_subsets::create_trie_subset,
};

use crate::{utils::keccak, EMPTY_HASH};

#[derive(Clone, Debug)]
pub struct MptNode(Vec<u8>);

#[derive(Default)]
pub struct Mpt {
    pub mpt: HashMap<B256, MptNode>,
    pub root: B256,
}

const EMPTY_TRIE_HASH: B256 = FixedBytes([
    86, 232, 31, 23, 27, 204, 85, 166, 255, 131, 69, 230, 146, 192, 248, 110, 91, 72, 224, 27, 153,
    108, 173, 192, 1, 98, 47, 181, 227, 99, 180, 33,
]);

impl Mpt {
    pub fn new() -> Self {
        Self {
            mpt: HashMap::new(),
            root: B256::default(),
        }
    }

    pub fn to_partial_trie(&self) -> HashedPartialTrie {
        let trie = self.to_partial_trie_helper(self.root);
        if trie == Node::Hash(crate::utils::compat::h256(EMPTY_TRIE_HASH)).into() {
            Node::Empty.into()
        } else {
            trie
        }
    }

    fn to_partial_trie_helper(&self, root: B256) -> HashedPartialTrie {
        let node = self.mpt.get(&root);
        let data = if let Some(mpt_node) = node {
            mpt_node.0.clone()
        } else {
            return Node::Hash(crate::utils::compat::h256(root)).into();
        };
        let a = <Vec<Vec<u8>>>::decode(&mut &*data).unwrap();
        match a.len() {
            17 => {
                let value = a[16].clone();
                let mut children = vec![];
                for it in a.iter().take(16) {
                    if it.is_empty() {
                        children.push(Node::Empty.into());
                        continue;
                    }
                    children.push(Arc::new(Box::new(
                        self.to_partial_trie_helper(B256::from_slice(it)),
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
                            self.to_partial_trie_helper(B256::from_slice(&a[1])),
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
                            self.to_partial_trie_helper(B256::from_slice(&a[1])),
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
                other => panic!("unexpected value {}", other),
            },
            other => panic!("unexpected length: {}", other),
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
        .insert(keccak(&rlp_node), MptNode(rlp_node.to_vec()));
    let a = <Vec<Vec<u8>> as alloy::rlp::Decodable>::decode(&mut &rlp_node[..]).unwrap();
    if a.len() == 2 {
        let prefix = a[0].clone();
        let is_leaf = (prefix[0] >> 4 == 2) || (prefix[0] >> 4 == 3);
        let mut nibbles = nibbles_from_hex_prefix_encoding(&prefix);
        loop {
            let mut node = vec![];
            alloy::rlp::encode_list::<_, [u8]>(
                &[&*nibbles.to_hex_prefix_encoding(is_leaf), &a[1]],
                &mut node,
            );
            mpt.mpt.insert(keccak(&node), MptNode(node));
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
        other => panic!("unexpected value: {}", other),
    }
}

pub fn apply_diffs(
    mut mpt: HashedPartialTrie,
    mut storage: HashMap<B256, HashedPartialTrie>,
    contract_code: &mut HashMap<B256, Vec<u8>>,
    trace: GethTrace,
) -> (HashedPartialTrie, HashMap<B256, HashedPartialTrie>) {
    let GethTrace::PreStateTracer(PreStateFrame::Diff(diff)) = trace else {
        panic!();
    };

    let empty_node = HashedPartialTrie::from(Node::Empty);

    for (addr, old) in &diff.pre {
        let key = keccak(addr.0);
        if !diff.post.contains_key(addr) {
            storage.remove(&key);
        } else {
            let new = diff.post.get(addr).unwrap();
            if old.storage.is_empty() && new.storage.is_empty() {
                continue;
            }
            let mut trie = storage.get(&key).unwrap().clone();
            for (k, v) in &old.storage {
                if !new.storage.contains_key(k) {
                    // dbg!(format!("Del {:?} {:?}", addr, k));
                    trie.delete(b256_2nibbles(*k)).unwrap();
                    // println!("Done Del {:?} {:?}", addr, k);
                } else {
                    let sanity = trie.get(b256_2nibbles(*k)).unwrap();
                    let sanity = U256::decode(&mut &*sanity).unwrap();

                    assert_eq!(sanity, into_uint(*v));
                    let w = *new.storage.get(k).unwrap();
                    trie.insert(b256_2nibbles(*k), alloy::rlp::encode(into_uint(w)))
                        .unwrap();
                }
            }
            for (k, v) in &new.storage {
                if !old.storage.contains_key(k) {
                    trie.insert(b256_2nibbles(*k), alloy::rlp::encode(into_uint(*v)))
                        .unwrap();
                }
            }
            storage.insert(key, trie);
        }
    }

    for (addr, new) in &diff.post {
        let key = keccak(addr.0);
        if !diff.pre.contains_key(addr) {
            let mut trie = HashedPartialTrie::from(Node::Empty);
            for (&k, v) in &new.storage {
                trie.insert(b256_2nibbles(k), alloy::rlp::encode(into_uint(*v)))
                    .unwrap();
            }
            storage.insert(key, trie);
        }
    }

    // Delete accounts that are not in the post state.
    for addr in diff.pre.keys() {
        if !diff.post.contains_key(addr) {
            mpt.delete(address2nibbles(*addr)).unwrap();
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
                        let h: B256 = keccak(&bytes);
                        contract_code.insert(h, bytes);
                        h
                    }
                })
                .unwrap_or(EMPTY_HASH);
            let account = AccountRlp {
                nonce: acc.nonce.unwrap_or_default().into(),
                balance: crate::utils::compat::u256(acc.balance.unwrap_or_default()),
                storage_root: storage
                    .get(&(keccak(addr.0)))
                    .unwrap_or(&empty_node.clone())
                    .hash(),
                code_hash: crate::utils::compat::h256(code_hash),
            };
            mpt.insert(
                address2nibbles(*addr),
                ethers::utils::rlp::encode(&account).to_vec(),
            ) // TODO(aatifsyed): make the required change to evm_arithmetization
            .unwrap();
        } else {
            let old = mpt
                .get(address2nibbles(*addr))
                .map(|d| ethers::utils::rlp::decode(d).unwrap())
                .unwrap_or(AccountRlp {
                    nonce: Default::default(),
                    balance: Default::default(),
                    storage_root: empty_node.hash(),
                    code_hash: crate::utils::compat::h256(EMPTY_HASH),
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
                        let h = keccak(&bytes);
                        contract_code.insert(h, bytes);
                        h
                    }
                })
                .map(crate::utils::compat::h256)
                .unwrap_or(old.code_hash);
            let account = AccountRlp {
                nonce: acc.nonce.map(Into::into).unwrap_or(old.nonce),
                balance: acc
                    .balance
                    .map(crate::utils::compat::u256)
                    .unwrap_or(old.balance),
                storage_root: storage
                    .get(&(keccak(addr.0)))
                    .map(|trie| trie.hash())
                    .unwrap_or(old.storage_root),
                code_hash,
            };
            mpt.insert(
                address2nibbles(*addr),
                ethers::utils::rlp::encode(&account).to_vec(),
            )
            .unwrap();
        }
    }

    (mpt, storage)
}

fn address2nibbles(addr: Address) -> Nibbles {
    Nibbles::from_bytes_be(keccak(addr.0).as_slice()).unwrap()
}

fn b256_2nibbles(k: B256) -> Nibbles {
    Nibbles::from_bytes_be(keccak(k.0).as_slice()).unwrap()
}

pub fn trim(
    trie: HashedPartialTrie,
    mut storage_mpts: HashMap<B256, HashedPartialTrie>,
    touched: BTreeMap<Address, AccountState>,
    has_storage_deletion: bool,
) -> (HashedPartialTrie, HashMap<B256, HashedPartialTrie>) {
    let tok = |addr: &Address| Nibbles::from_bytes_be(keccak(addr.0).as_slice()).unwrap();
    let keys = touched.keys().map(tok).collect::<Vec<_>>();
    let new_state_trie = create_trie_subset(&trie, keys).unwrap();
    if has_storage_deletion {
        // TODO: This is inefficient. Replace with a smarter solution.
        return (new_state_trie, storage_mpts);
    }
    let keys_to_addrs = touched
        .keys()
        .map(|addr| ((keccak(addr.0)), *addr))
        .collect::<HashMap<_, _>>();
    for (k, t) in storage_mpts.iter_mut() {
        if !keys_to_addrs.contains_key(k) {
            *t = HashedPartialTrie::from(Node::Hash(t.hash()));
        } else {
            let addr = keys_to_addrs.get(k).unwrap();
            let acc = touched.get(addr).unwrap();
            let keys = acc
                .storage
                .keys()
                .map(|slot| Nibbles::from_bytes_be(keccak(slot.0).as_slice()).unwrap())
                .collect::<Vec<_>>();

            if let Ok(trie) = create_trie_subset(t, keys) {
                *t = trie;
            }
        }
    }
    (new_state_trie, storage_mpts)
}

fn into_uint(hash: B256) -> U256 {
    U256::from_be_bytes(*hash) // TODO(aatifsyed): is this
                               // right?
}
