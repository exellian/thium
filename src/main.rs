use base64::Engine;
use base64::prelude::BASE64_STANDARD;
use pqc_dilithium::{Keypair, PUBLICKEYBYTES, SECRETKEYBYTES, SIGNBYTES};

struct Transaction {
    timestamp: u128,
    sender: [u8;PUBLICKEYBYTES],
    receiver: [u8;PUBLICKEYBYTES],
    amount: u128,
    signature: [u8;SIGNBYTES]
}

struct Block {
    version: u32,
    bits: u32,
    previous_block_hash: [u8;512],
    transactions: Vec<Transaction>
}

struct BlockChallenge {
    block_hash: [u8;512],
    nonce: u64
}

struct BlockAdvertisement {
    block: Block
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
}