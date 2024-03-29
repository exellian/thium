use std::cmp::Ordering;
use std::{io, mem, thread};
use std::collections::{HashMap};
use std::fmt::{Display, Formatter};
use std::io::{Cursor, Write};
use std::ops::{Range, Rem, Div};
use std::sync::atomic;
use std::sync::atomic::AtomicBool;
use base64::Engine;
use base64::prelude::BASE64_STANDARD;
use pqc_dilithium::{Keypair, PUBLICKEYBYTES, SECRETKEYBYTES, SIGNBYTES};
use rand::RngCore;
use ripemd::Ripemd160;
use sha2::{Digest, Sha256, Sha512};

fn hash_sha512(bytes: &[u8]) -> [u8;64] {
    let mut hasher = Sha512::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

fn hash_ripemd160(bytes: &[u8]) -> [u8;20] {
    let mut hasher = Ripemd160::new();
    hasher.update(bytes);
    hasher.finalize().into()
}

pub fn write(arr: &mut [u8], range: Range<usize>, bytes: &[u8]) -> io::Result<usize> {
    let mut cursor = Cursor::new(&mut arr[range]);
    cursor.write(bytes)
}

struct Address(RipeMd160Hash);
impl Address {

    pub const SIZE: usize = 20;

    #[inline]
    pub fn hash(public_key: &[u8;PUBLICKEYBYTES]) -> [u8;20] {
        hash_ripemd160(&hash_sha512(public_key))
    }
}

/// A raw transaction input has the following layout
/// |------------------------------------------|
/// | previous_transaction_hash: 64 bytes      |
/// |------------------------------------------|
/// | previous_transaction_index: 4 bytes l.e. |
/// |------------------------------------------|
struct TransactionInput<'a>(&'a [u8]);

impl<'a> TransactionInput<'a> {

    const SIZE: usize = Self::PREVIOUS_TRANSACTION_HASH_SIZE + Self::PREVIOUS_TRANSACTION_INDEX_SIZE;

    const PREVIOUS_TRANSACTION_HASH_SIZE: usize = Sha512Hash::SIZE;
    const PREVIOUS_TRANSACTION_HASH_OFFSET: usize = 0;

    const PREVIOUS_TRANSACTION_INDEX_SIZE: usize = mem::size_of::<u32>();
    const PREVIOUS_TRANSACTION_INDEX_OFFSET: usize = Self::PREVIOUS_TRANSACTION_HASH_OFFSET + Self::PREVIOUS_TRANSACTION_HASH_SIZE;
}


/// A raw transaction has the following layout
/// |----------------------------------|
/// | amount: 16 bytes l.e.            |
/// |----------------------------------|
/// | receiver_address: 20 bytes l.e.  |
/// |----------------------------------|
struct TransactionOutput<'a>(&'a [u8]);

impl<'a> TransactionOutput<'a> {

    const SIZE: usize = Self::AMOUNT_SIZE + Self::RECEIVER_ADDRESS_SIZE;

    const AMOUNT_SIZE: usize = mem::size_of::<u128>();
    const AMOUNT_OFFSET: usize = 0;

    const RECEIVER_ADDRESS_SIZE: usize = Address::SIZE;
    const RECEIVER_ADDRESS_OFFSET: usize = Self::AMOUNT_OFFSET + Self::AMOUNT_SIZE;
}

/// A raw transaction has the following layout
/// |----------------------------|
/// | owner: PUBLIC_KEY_BYTES    |
/// |----------------------------|
/// | signature: SIGN_BYTES      |
/// |----------------------------|
/// | input_count: 4 bytes l.e.  |
/// |----------------------------|
/// | output_count: 4 bytes l.e. |
/// |----------------------------|
/// | inputs...                  |
/// |----------------------------|
/// | outputs...                 |
/// |----------------------------|
struct Transaction<'a>(&'a [u8]);

impl<'a> Transaction<'a> {

    pub const fn size(input_count: usize, output_count: usize) -> usize {
        return Self::HEADER_SIZE + TransactionInput::SIZE * input_count + TransactionOutput::SIZE * output_count;
    }

    const HEADER_SIZE: usize = Self::OWNER_SIZE + Self::SIGNATURE_SIZE + Self::INPUT_COUNT_SIZE + Self::OUTPUT_COUNT_SIZE;

    const OWNER_SIZE: usize = PUBLICKEYBYTES;
    const OWNER_OFFSET: usize = 0;

    const SIGNATURE_SIZE: usize = SIGNBYTES;
    const SIGNATURE_OFFSET: usize = Self::OWNER_OFFSET + Self::OWNER_SIZE;

    const INPUT_COUNT_SIZE: usize = mem::size_of::<u32>();
    const INPUT_COUNT_OFFSET: usize = Self::SIGNATURE_OFFSET + Self::SIGNATURE_SIZE;

    const OUTPUT_COUNT_SIZE: usize = mem::size_of::<u32>();
    const OUTPUT_COUNT_OFFSET: usize = Self::INPUT_COUNT_OFFSET;

}

/// A raw block has the following layout
/// |------------------------------------------|
/// | version: 4 bytes l.e                     |
/// |------------------------------------------|
/// | difficulty_bits: 8 bytes                 |
/// |------------------------------------------|
/// | timestamp: 16 bytes l.e.                 |
/// |------------------------------------------|
/// | previous_challenge_block_hash: 64 bytes  |
/// |------------------------------------------|
/// | nonce: 16 bytes l.e                      |
/// |------------------------------------------|
/// | transaction_count: 4 bytes l.e           |
/// |------------------------------------------|
/// | transaction...                           |
/// |                                          |
struct Block<'a>(&'a [u8]);
struct BlockMut<'a>(&'a mut [u8]);

impl<'a> Block<'a> {
    pub const HEADER_SIZE: usize = Self::VERSION_SIZE + Self::DIFFICULTY_BITS_SIZE + Self::TIMESTAMP_SIZE + Self::PREVIOUS_CHALLENGE_BLOCK_HASH_SIZE + Self::NONCE_SIZE + Self::TRANSACTION_COUNT_SIZE;
    pub const fn size(transaction_sizes: &[(usize, usize)]) -> usize {
        let transactions_size: usize = transaction_sizes.iter().map(|(input_count, output_count)| Transaction::size(*input_count, *output_count)).sum();
        return Self::HEADER_SIZE + transactions_size;
    } 
    pub const VERSION_SIZE: usize = mem::size_of::<u32>();
    pub const VERSION_OFFSET: usize = 0;

    pub const DIFFICULTY_BITS_SIZE: usize = mem::size_of::<u64>();
    pub const DIFFICULTY_BITS_OFFSET: usize = Self::VERSION_OFFSET + Self::VERSION_SIZE;

    pub const TIMESTAMP_SIZE: usize = mem::size_of::<u128>();
    pub const TIMESTAMP_OFFSET: usize = Self::DIFFICULTY_BITS_OFFSET + Self::DIFFICULTY_BITS_SIZE;

    pub const PREVIOUS_CHALLENGE_BLOCK_HASH_SIZE: usize = Sha512Hash::SIZE;
    pub const PREVIOUS_CHALLENGE_BLOCK_HASH_OFFSET: usize = Self::TIMESTAMP_OFFSET + Self::TIMESTAMP_SIZE;

    pub const NONCE_SIZE: usize = mem::size_of::<u128>();
    pub const NONCE_OFFSET: usize = Self::PREVIOUS_CHALLENGE_BLOCK_HASH_OFFSET + Self::PREVIOUS_CHALLENGE_BLOCK_HASH_SIZE;

    pub const TRANSACTION_COUNT_SIZE: usize = mem::size_of::<u32>();
    pub const TRANSACTION_COUNT_OFFSET: usize = Self::NONCE_OFFSET + Self::NONCE_SIZE;

    #[inline]
    pub fn read<const SIZE: usize>(&self, range: Range<usize>) -> &[u8;SIZE] {
        debug_assert!(range.len() == SIZE);
        self.0[range].try_into().unwrap()
    }

    #[inline]
    pub fn hash(&self) -> Sha512Hash {
        Sha512Hash(hash_sha512(self.0))
    }

}

impl<'a> BlockMut<'a> {

    pub fn set_nonce(&mut self, nonce: u128) {
        write(&mut self.0, Block::NONCE_OFFSET..Block::NONCE_OFFSET + Block::NONCE_SIZE, &nonce.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn hash(&self) -> Sha512Hash {
        Block(self.0).hash()
    }

    #[inline]
    pub fn challenge_count(&self) -> u32 {
        Block(self.0).challenge_count()
    }
}

/// A raw challenge block has the following layout
/// |------------------------------------|
/// | root_block_hash: 64 bytes          |
/// |------------------------------------|
/// | challenge_block_hash: 64 bytes     |
/// |------------------------------------|
struct BlockChallenge<'a>(&'a [u8]);
struct BlockChallengeMut<'a>(&'a mut [u8]);

impl<'a> BlockChallenge<'a> {

    pub const SIZE: usize = Self::ROOT_BLOCK_HASH_SIZE + Self::CHALLENGE_BLOCK_HASH_SIZE;
    
    const ROOT_BLOCK_HASH_SIZE: usize = Sha512Hash::SIZE;
    const ROOT_BLOCK_HASH_OFFSET: usize = 0;
    
    const CHALLENGE_BLOCK_HASH_SIZE: usize = Sha512Hash::SIZE;
    const CHALLENGE_BLOCK_HASH_OFFSET: usize = Self::ROOT_BLOCK_HASH_OFFSET + Self::ROOT_BLOCK_HASH_SIZE;
    
    #[inline]
    pub fn hash(&self) -> Sha512Hash {
        Sha512Hash(hash_sha512(&self.0))
    }
}

impl<'a> BlockChallengeMut<'a> {
    
    #[inline]
    pub fn set_root_block_hash(&mut self, bytes: &[u8;BlockChallenge::ROOT_BLOCK_HASH_SIZE]) {
        write(&mut self.0, BlockChallenge::ROOT_BLOCK_HASH_OFFSET..BlockChallenge::ROOT_BLOCK_HASH_OFFSET + BlockChallenge::ROOT_BLOCK_HASH_SIZE, bytes).unwrap();
    }
    
    pub fn set_challenge_block_hash(&mut self, bytes: &[u8;BlockChallenge::CHALLENGE_BLOCK_HASH_SIZE]) {
        write(&mut self.0, BlockChallenge::CHALLENGE_BLOCK_HASH_OFFSET..BlockChallenge::CHALLENGE_BLOCK_HASH_OFFSET  + BlockChallenge::CHALLENGE_BLOCK_HASH_SIZE, bytes).unwrap();
    }

    #[inline]
    pub fn hash(&self) -> Sha512Hash {
        BlockChallenge(&self.0).hash()
    }
}

#[derive(PartialEq)]
struct RipeMd160Hash([u8; RipeMd160Hash::SIZE]);

impl RipeMd160Hash {

    pub const SIZE: usize = 20;

    pub fn new(data: [u8;Self::SIZE]) -> Self {
        RipeMd160Hash(data)
    }
}

#[derive(PartialEq)]
struct Sha512Hash([u8; Sha512Hash::SIZE]);

impl Sha512Hash {

    pub const SIZE: usize = 64;

    pub fn new(data: [u8;Self::SIZE]) -> Self {
        Sha512Hash(data)
    }

}

impl Div<u64> for Sha512Hash {
    type Output = Self;

    fn div(self, rhs: u64) -> Self::Output {
        let mut quotient_bytes = [0u8; 64];
        let mut remainder: u64 = 0;

        for i in (0..64).rev() {
            let dividend = (remainder << 8) | self.0[i] as u64;
            quotient_bytes[i] = (dividend / rhs) as u8;
            remainder = dividend % rhs;
        }

        Sha512Hash(quotient_bytes)
    }
}

impl PartialEq<u64> for Sha512Hash {
    fn eq(&self, other: &u64) -> bool {
        let bytes = other.to_le_bytes();
        for i in 0..mem::size_of::<u64>() {
            if self.0[i] != bytes[i] {
                return false;
            }
        }
        true
    }
}

impl PartialOrd<u64> for Sha512Hash
{
    fn partial_cmp(&self, other: &u64) -> Option<Ordering> {
        let bytes = other.to_le_bytes();
        for i in mem::size_of::<u64>() - 1..0 {
            if self.0[i] < bytes[i] {
                return Some(Ordering::Less);
            } else if self.0[i] > bytes[i] {
                return Some(Ordering::Greater);
            }
        }
        Some(Ordering::Equal)
    }
}

impl Rem<u64> for Sha512Hash {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        let mut quotient_bytes = [0u8; 64];
        let mut remainder: u64 = 0;

        for i in (0..64).rev() {
            let dividend = (remainder << 8) | self.0[i] as u64;
            quotient_bytes[i] = (dividend / rhs) as u8;
            remainder = dividend % rhs;
        }
        remainder
    }
}

impl Display for Sha512Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", BASE64_STANDARD.encode(&self.0))
    } 
}

impl PartialOrd for Sha512Hash {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        for i in 0..Self::SIZE {
            if &self.0[i] > &other.0[i] {
                return Some(Ordering::Greater);
            } else if &self.0[i] < &other.0[i] {
                return Some(Ordering::Less);
            }
        }
        Some(Ordering::Equal)
    }
}

trait UTXODatabase {

}

trait Blockchain {

    type Error;

    fn get(&self, index: u64) -> Vec<u8>;
    fn try_add(&self, block: Block) -> Result<(), Self::Error>;
    fn len(&self) -> u64;
}

fn mine_challenge(new_block: &mut BlockMut, blockchain: &impl Blockchain) -> Vec<u8> {
    let blockchain_len = blockchain.len();
    let challenge_count = new_block.challenge_count();
    let nonce = rand::random();
    new_block.set_nonce(nonce);
    
    let mut challenge_buffer = vec![0u8;BlockChallenge::SIZE];
    let mut challenge = BlockChallengeMut(&mut challenge_buffer);
    let mut block_hash = new_block.hash();
    challenge.set_root_block_hash(&block_hash.0);
    
    // Retrieve the pair block
    let block_index = block_hash % blockchain_len;
    let mut block = BlockMut(&mut blockchain.get(block_index));
    block.set_nonce(nonce);
    challenge.set_challenge_block_hash()
        // Write block challenge to block challenge index position
        challenge.set_challenge_block_hash(challenge_idx, &block_hash.0);
    }
    challenge_buffer
}

/// Returns a block-challenge with a hash that fulfills the difficulty
fn mine(block: &mut BlockMut) -> (Sha512Hash, Vec<u8>) {

    const AMOUNT_OF_THREADS: usize = 4;
    let raw_block = Block::from(block);
    let block_hash: Sha512Hash = raw_block.hash();

    println!("Hash: {}", &block_hash);
    let should_exit = AtomicBool::new(false);
    thread::scope(|scope| {
        let mut handles = vec![];
        for _ in 0..AMOUNT_OF_THREADS {
            handles.push(scope.spawn(|| {
                let mut challenge = BlockChallenge::new(&block_hash, 0);
                while !should_exit.load(atomic::Ordering::Acquire) {
                    let res = challenge.hash();
                    if &res < &block.header.difficulty {
                        println!("Found new block: {}", res);
                        should_exit.store(true, atomic::Ordering::Release);
                        return Some(challenge.nonce);
                    }
                    challenge.nonce = ;
                }
                None
            }));
        }
        for handle in handles {
            if let Some(res) = handle.join().unwrap() {
                return res;
            }
        }
        unreachable!()
    })
}

fn main() {
    let keys = Keypair::generate();
    println!("Private: {} Public: {} Signature: {}", SECRETKEYBYTES, PUBLICKEYBYTES, SIGNBYTES);
    assert!(keys.public.len() == PUBLICKEYBYTES);
    assert!(keys.expose_secret().len() == SECRETKEYBYTES);

    let msg = "HALLO".as_bytes();
    let signature = keys.sign(msg);

    let sig_str = BASE64_STANDARD.encode(signature);
    println!("Signature: {}", sig_str);

    let nonce = mine(&last_block);
}