// use eth_trie_utils::nibbles::Nibbles;
// use eth_trie_utils::partial_trie::{HashedPartialTrie, Node};
// use ethers::prelude::*;
// use ethers::utils::rlp::RlpStream;
// use ethers::utils::{keccak256, rlp};
// use plonky2_evm::generation::mpt::AccountRlp;
// use std::collections::HashMap;
// use std::sync::Arc;
//
// #[derive(Debug)]
// pub enum Leaf {
//     Account(AccountRlp),
//     Value(U256),
// }
//
// impl Leaf {
//     pub fn encode(&self) -> Vec<u8> {
//         match self {
//             Leaf::Account(acc) => rlp::encode(acc).to_vec(),
//             Leaf::Value(v) => rlp::encode(v).to_vec(),
//         }
//     }
//
//     pub fn decode(bytes: &[u8]) -> Self {
//         match rlp::decode::<AccountRlp>(bytes) {
//             Ok(acc) => Leaf::Account(acc),
//             Err(_) => Leaf::Value(rlp::decode(bytes).unwrap()),
//         }
//     }
// }
//
// #[derive(Debug)]
// pub enum MptNode {
//     Leaf(Nibbles, Leaf),
//     Extension(Nibbles, H256),
//     Branch([H256; 16], Vec<u8>),
//     Hash(H256),
// }
//
// impl MptNode {
//     pub fn is_hash(&self) -> bool {
//         matches!(self, MptNode::Hash(_))
//     }
//
//     pub fn hash(&self) -> H256 {
//         match self {
//             MptNode::Leaf(nibs, acc) => {
//                 let hex_prefix_k = nibs.to_hex_prefix_encoding(true);
//                 let mut stream = RlpStream::new_list(2);
//
//                 stream.append(&hex_prefix_k);
//                 stream.append(&acc.encode());
//
//                 let bytes = stream.out().to_vec();
//                 assert!(bytes.len() >= 32);
//                 H256(keccak256(bytes))
//             }
//             MptNode::Extension(nibs, h) => {
//                 let hex_prefix_k = nibs.to_hex_prefix_encoding(false);
//                 let mut stream = RlpStream::new_list(2);
//
//                 stream.append(&hex_prefix_k);
//                 stream.append(&h.0.as_ref());
//
//                 let bytes = stream.out().to_vec();
//                 assert!(bytes.len() >= 32);
//                 H256(keccak256(bytes))
//             }
//             MptNode::Branch(hs, v) => {
//                 let mut stream = RlpStream::new_list(17);
//
//                 for h in hs.iter() {
//                     if h.is_zero() {
//                         stream.append_empty_data();
//                     } else {
//                         stream.append(&h.0.as_ref());
//                     }
//                 }
//
//                 match v.is_empty() {
//                     false => stream.append(v),
//                     true => stream.append_empty_data(),
//                 };
//
//                 let bytes = stream.out().to_vec();
//                 assert!(bytes.len() >= 32);
//                 H256(keccak256(bytes))
//             }
//             MptNode::Hash(h) => *h,
//         }
//     }
// }
//
// pub struct Mpt {
//     pub mpt: HashMap<H256, MptNode>,
//     pub root: H256,
// }
//
// impl Mpt {
//     pub fn new() -> Self {
//         Self {
//             mpt: HashMap::new(),
//             root: H256::zero(),
//         }
//     }
//
//     pub fn to_partial_trie(&self) -> HashedPartialTrie {
//         self.to_partial_trie_helper(self.root)
//     }
//     fn to_partial_trie_helper(&self, root: H256) -> HashedPartialTrie {
//         let node = self.mpt.get(&root).unwrap();
//         match node {
//             MptNode::Leaf(nibs, acc) => {
//                 Node::Leaf {
//                     nibbles: *nibs,
//                     value: acc.encode(),
//                 }
//                 .into()
//             }
//             MptNode::Extension(nibs, h) => Node::Extension {
//                 nibbles: *nibs,
//                 child: Arc::new(Box::new(self.to_partial_trie_helper(*h))),
//             }
//             .into(),
//             MptNode::Branch(hs, v) => {
//                 let mut children = vec![];
//                 for i in 0..16 {
//                     if hs[i].is_zero() {
//                         children.push(Node::Empty.into());
//                         continue;
//                     }
//                     children.push(Arc::new(Box::new(self.to_partial_trie_helper(hs[i]))));
//                 }
//                 Node::Branch {
//                     value: v.clone(),
//                     children: children.try_into().unwrap(),
//                 }
//                 .into()
//             }
//             MptNode::Hash(h) => Node::Hash(*h).into(),
//         }
//     }
// }
//
// pub fn insert_mpt(mpt: &mut Mpt, proof: Vec<Bytes>) {
//     for p in proof.into_iter() {
//         let a = rlp::decode_list::<Vec<u8>>(&p);
//         let node = match a.len() {
//             17 => {
//                 let value = a[16].clone();
//                 let mut children = vec![];
//                 for i in 0..16 {
//                     if a[i].is_empty() {
//                         children.push(H256::zero());
//                         continue;
//                     }
//                     let h = H256::from_slice(&a[i]);
//                     mpt.mpt.entry(h).or_insert(MptNode::Hash(h));
//                     children.push(h);
//                 }
//                 MptNode::Branch(children.try_into().unwrap(), value)
//             }
//             2 => match a[0][0] >> 4 {
//                 0 => {
//                     let ext_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
//                     let h = H256::from_slice(&a[1]);
//                     mpt.mpt.entry(h).or_insert(MptNode::Hash(h));
//                     MptNode::Extension(ext_prefix, h)
//                 }
//                 1 => {
//                     let b = a[0][0] & 0xf;
//                     let mut ext_prefix = if a[0].len() > 1 {
//                         Nibbles::from_bytes_be(&a[0][1..]).unwrap()
//                     } else {
//                         Nibbles {
//                             count: 0,
//                             packed: U512::zero(),
//                         }
//                     };
//                     ext_prefix.push_nibble_front(b);
//
//                     let h = H256::from_slice(&a[1]);
//                     mpt.mpt.entry(h).or_insert(MptNode::Hash(h));
//
//                     MptNode::Extension(ext_prefix, h)
//                 }
//                 2 => {
//                     let leaf_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
//                     MptNode::Leaf(leaf_prefix, Leaf::decode(&a[1]))
//                 }
//                 3 => {
//                     let b = a[0][0] & 0xf;
//                     let mut leaf_prefix = Nibbles::from_bytes_be(&a[0][1..]).unwrap();
//                     leaf_prefix.push_nibble_front(b);
//
//                     dbg!(&a);
//                     MptNode::Leaf(leaf_prefix, Leaf::decode(&a[1]))
//                 }
//                 _ => panic!("wtf?"),
//             },
//             _ => panic!("wtf?"),
//         };
//         let h = H256(keccak256(&p));
//         assert_eq!(h, node.hash());
//         mpt.mpt.insert(h, node);
//     }
// }
