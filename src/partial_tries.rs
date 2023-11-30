// use std::collections::HashSet;
//
// use anyhow::Result;
// use eth_trie_utils::nibbles::Nibbles;
// use eth_trie_utils::partial_trie::{HashedPartialTrie, PartialTrie};
// use ethers::prelude::*;
// use ethers::utils::rlp;
//
// /// Reconstruct a Merkle-Patricia partial trie from a MPT proof.
// /// Can be an account proof for the state MPT or a storage proof for the storage MPT.
// pub fn insert_proof(
//     trie: &mut HashedPartialTrie,
//     key: [u8; 32],
//     proof: Vec<Bytes>,
//     insert_leaf: bool,
//     dont_touch_these_nibbles: &mut HashSet<Nibbles>,
// ) -> Result<()> {
//     let mut nibbles = Nibbles::from_bytes_be(&key)?;
//     let mut current_prefix = Nibbles {
//         count: 0,
//         packed: U256::zero(),
//     };
//     let proof_len = proof.len();
//     for (p_ind, p) in proof.into_iter().enumerate() {
//         let a = rlp::decode_list::<Vec<u8>>(&p);
//         match a.len() {
//             17 => {
//                 let nibble = nibbles.pop_next_nibble_front();
//                 for i in 0..16 {
//                     let mut new_prefix = current_prefix;
//                     new_prefix.push_nibble_back(i);
//                     if insert_leaf && i == nibble {
//                         dont_touch_these_nibbles.insert(new_prefix);
//                         continue;
//                     }
//                     // if !insert_leaf && (p_ind < proof_len - 1) && i == nibble {
//                     //     continue;
//                     // }
//                     if dont_touch_these_nibbles.contains(&new_prefix) {
//                         continue;
//                     }
//                     if !a[i as usize].is_empty()
//                         && !trie.is_not_empty_or_hash(&mut new_prefix.clone())
//                     {
//                         let hash = H256::from_slice(&a[i as usize]);
//                         trie.insert(new_prefix, hash);
//                     }
//                 }
//                 current_prefix.push_nibble_back(nibble);
//             }
//             2 => match a[0][0] >> 4 {
//                 0 => {
//                     let ext_prefix = &a[0][1..];
//                     for &byte in ext_prefix {
//                         let b = byte >> 4;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                         let b = byte & 0xf;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                     }
//                     if !insert_leaf && p_ind == proof_len - 1 {
//                         assert!(!a[1].is_empty());
//                         trie.insert(current_prefix, H256::from_slice(&a[1]));
//                     }
//                 }
//                 1 => {
//                     let b = a[0][0] & 0xf;
//                     let nibble = nibbles.pop_next_nibble_front();
//                     if insert_leaf {
//                         assert_eq!(b, nibble);
//                     }
//                     current_prefix.push_nibble_back(b);
//                     let ext_prefix = &a[0][1..];
//                     for &byte in ext_prefix {
//                         let b = byte >> 4;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                         let b = byte & 0xf;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                     }
//                     if !insert_leaf && p_ind == proof_len - 1 {
//                         assert!(!a[1].is_empty());
//                         trie.insert(current_prefix, H256::from_slice(&a[1]));
//                     }
//                 }
//                 2 => {
//                     let leaf_prefix = &a[0][1..];
//                     for &byte in leaf_prefix {
//                         let b = byte >> 4;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                         let b = byte & 0xf;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                     }
//                     if insert_leaf {
//                         assert_eq!(current_prefix, Nibbles::from_bytes_be(&key)?);
//                     }
//                     trie.insert(current_prefix, a[1].clone());
//                 }
//                 3 => {
//                     let b = a[0][0] & 0xf;
//                     let nibble = nibbles.pop_next_nibble_front();
//                     if insert_leaf {
//                         assert_eq!(b, nibble);
//                     }
//                     current_prefix.push_nibble_back(b);
//                     let leaf_prefix = &a[0][1..];
//                     for &byte in leaf_prefix {
//                         let b = byte >> 4;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                         let b = byte & 0xf;
//                         let nibble = nibbles.pop_next_nibble_front();
//                         if insert_leaf {
//                             assert_eq!(b, nibble);
//                         }
//                         current_prefix.push_nibble_back(b);
//                     }
//                     if insert_leaf {
//                         assert_eq!(current_prefix, Nibbles::from_bytes_be(&key)?);
//                     }
//                     trie.insert(current_prefix, a[1].clone());
//                 }
//                 _ => panic!("wtf?"),
//             },
//             _ => panic!("wtf?"),
//         }
//     }
//
//     Ok(())
// }
