use std::{io, mem, thread};
use std::error::Error;
use std::fmt::{Display, Formatter};
use std::hash::{DefaultHasher, Hash, Hasher};
use std::io::{Cursor, Write};
use std::ops::{Range, Rem, RangeFrom};
use std::sync::{atomic};
use std::sync::atomic::AtomicBool;
use std::time::{Duration, SystemTime};
use pqc_dilithium::{Keypair, PUBLICKEYBYTES, SECRETKEYBYTES, SIGNBYTES};
use primitive_types::U512;
use ripemd::Ripemd160;
use sha2::{Digest, Sha512};
use sled::Db;
use libp2p::{gossipsub, mdns, noise, swarm::NetworkBehaviour, swarm::SwarmEvent, tcp, yamux};
use libp2p::futures::StreamExt;
use tokio::select;
use tracing_subscriber::EnvFilter;

fn hash_sha512(bytes: &[u8]) -> U512 {
    let mut hasher = Sha512::new();
    hasher.update(bytes);
    U512::from_little_endian(hasher.finalize().as_ref())
}

fn hash_sha512_1(bytes: &[u8]) -> [u8;Sha512Hash::SIZE] {
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
pub fn write2(arr: &mut [u8], range: Range<usize>, one: &[u8], second: &[u8]) -> io::Result<usize> {
    let mut cursor = Cursor::new(&mut arr[range]);
    cursor.write(one)?;
    cursor.write(second)
}

pub fn write1(arr: &mut [u8], range: RangeFrom<usize>, bytes: &[u8]) -> io::Result<usize> {
    let mut cursor = Cursor::new(&mut arr[range]);
    cursor.write(bytes)
}

/// Hash: x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
/// Difficulty: 0x 00                       00 FFF0 0F00 0000
///                Exponent 1bytes (0-114)  Coefficient 7 bytes (14 nibbles)
/// 64 - 7 
fn fulfills_difficulty(hash: &Sha512Hash, difficulty_bits: u64) -> bool {
    let exponent = (difficulty_bits >> 56) as usize;
    let coefficient = difficulty_bits & 0x00FFFFFFFFFFFFFF;
    let difficulty = U512::from(coefficient) << exponent * 4;
    hash.0 < difficulty
}

struct Address(RipeMd160Hash);
impl Address {

    pub const SIZE: usize = 20;

    #[inline]
    pub fn hash(public_key: &[u8;PUBLICKEYBYTES]) -> [u8;20] {
        let hash = hash_sha512_1(public_key);
        hash_ripemd160(&hash)
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
struct TransactionOutputMut<'a>(&'a mut [u8]);
impl<'a> TransactionOutput<'a> {

    const SIZE: usize = Self::AMOUNT_SIZE + Self::RECEIVER_ADDRESS_SIZE;

    const AMOUNT_SIZE: usize = mem::size_of::<u128>();
    const AMOUNT_OFFSET: usize = 0;

    const RECEIVER_ADDRESS_SIZE: usize = Address::SIZE;
    const RECEIVER_ADDRESS_OFFSET: usize = Self::AMOUNT_OFFSET + Self::AMOUNT_SIZE;
}
impl<'a> TransactionOutputMut<'a> {

    #[inline]
    pub fn set_amount(&mut self, amount: u128) {
        write(&mut self.0, TransactionOutput::AMOUNT_OFFSET..TransactionOutput::AMOUNT_OFFSET + TransactionOutput::AMOUNT_SIZE, &amount.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_receiver_address(&mut self, receiver: &Address) {
        write(&mut self.0, TransactionOutput::RECEIVER_ADDRESS_OFFSET..TransactionOutput::RECEIVER_ADDRESS_OFFSET + TransactionOutput::RECEIVER_ADDRESS_SIZE, &receiver.0.0).unwrap();
    }
}

/// A raw transaction has the following layout
/// |----------------------------|
/// | owner: PUBLIC_KEY_BYTES    |
/// |----------------------------|
/// | input_count: 4 bytes l.e.  |
/// |----------------------------|
/// | output_count: 4 bytes l.e. |
/// |----------------------------|
/// | inputs...                  |
/// |----------------------------|
/// | outputs...                 |
/// |----------------------------|
/// |----------------------------|
/// | signature: SIGN_BYTES      |
/// |----------------------------|
struct Transaction<'a>(&'a [u8]);
struct TransactionMut<'a>(&'a mut [u8]);

impl<'a> Transaction<'a> {

    pub const fn size(input_count: usize, output_count: usize) -> usize {
        return Self::HEADER_SIZE + TransactionInput::SIZE * input_count + TransactionOutput::SIZE * output_count + Self::SIGNATURE_SIZE;
    }

    const HEADER_SIZE: usize = Self::OWNER_SIZE + Self::INPUT_COUNT_SIZE + Self::OUTPUT_COUNT_SIZE;

    const OWNER_SIZE: usize = PUBLICKEYBYTES;
    const OWNER_OFFSET: usize = 0;

    const SIGNATURE_SIZE: usize = SIGNBYTES;
    fn signature_offset(input_count: usize, output_count: usize) -> usize {
        Self::HEADER_SIZE + TransactionInput::SIZE * input_count + TransactionOutput::SIZE * output_count
    }

    const INPUT_COUNT_SIZE: usize = mem::size_of::<u32>();
    const INPUT_COUNT_OFFSET: usize = Self::OWNER_OFFSET + Self::OWNER_SIZE;

    const OUTPUT_COUNT_SIZE: usize = mem::size_of::<u32>();
    const OUTPUT_COUNT_OFFSET: usize = Self::INPUT_COUNT_OFFSET + Self::INPUT_COUNT_SIZE;

    const INPUT_OUTPUT_OFFSET: usize = Self::OUTPUT_COUNT_OFFSET + Self::OUTPUT_COUNT_SIZE;

    pub fn hash(&self) -> [u8;Sha512Hash::SIZE] {
        hash_sha512_1(&self.0[0..self.0.len() - Self::SIGNATURE_SIZE])
    }

}

impl<'a> TransactionMut<'a> {

    #[inline]
    pub fn set_owner(&mut self, owner: &[u8;PUBLICKEYBYTES]) {
        write(&mut self.0, Transaction::OWNER_OFFSET..Transaction::OWNER_OFFSET + Transaction::OWNER_SIZE, owner).unwrap();
    }

    #[inline]
    pub fn set_input_count(&mut self, input_count: u32) {
        write(&mut self.0, Transaction::INPUT_COUNT_OFFSET..Transaction::INPUT_COUNT_OFFSET + Transaction::INPUT_COUNT_SIZE, &input_count.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_output_count(&mut self, output_count: u32) {
        write(&mut self.0, Transaction::OUTPUT_COUNT_OFFSET..Transaction::OUTPUT_COUNT_OFFSET + Transaction::OUTPUT_COUNT_SIZE, &output_count.to_le_bytes()).unwrap();
    }

    pub fn set_inputs_outputs(&mut self, inputs: &[u8], outputs: &[u8]) {
        let len = self.0.len();
        write2(&mut self.0, Transaction::INPUT_OUTPUT_OFFSET..len - Transaction::SIGNATURE_SIZE, inputs, outputs).unwrap();
    }

    pub fn set_signature(&mut self, signature: &[u8;SIGNBYTES]) {
        let len = self.0.len();
        write1(&mut self.0, len - Transaction::SIGNATURE_SIZE.., signature).unwrap();
    }

    #[inline]
    pub fn hash(&self) -> [u8;Sha512Hash::SIZE] {
        Transaction(self.0).hash()
    }
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
#[derive(Copy, Clone)]
struct Block<'a>(&'a [u8]);
struct BlockMut<'a>(&'a mut [u8]);

impl<'a> Block<'a> {
    pub const HEADER_SIZE: usize = Self::VERSION_SIZE + Self::DIFFICULTY_BITS_SIZE + Self::TIMESTAMP_SIZE + Self::PREVIOUS_CHALLENGE_BLOCK_HASH_SIZE + Self::NONCE_SIZE + Self::TRANSACTION_COUNT_SIZE;
    pub fn size(transaction_sizes: &[(usize, usize)]) -> usize {
        let mut transactions_size: usize = 0;
        for (input_count, output_count) in transaction_sizes {
            transactions_size += Transaction::size(*input_count, *output_count);
        }
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

    pub const TRANSACTIONS_OFFSET: usize = Self::TRANSACTION_COUNT_OFFSET + Self::TRANSACTION_COUNT_SIZE;

    #[inline]
    pub fn read<const SIZE: usize>(&self, range: Range<usize>) -> &[u8;SIZE] {
        debug_assert!(range.len() == SIZE);
        self.0[range].try_into().unwrap()
    }

    #[inline]
    pub fn hash(&self) -> Sha512Hash {
        Sha512Hash(hash_sha512(self.0))
    }
    
    #[inline]
    pub fn difficulty_bits(&self) -> u64 {
        u64::from_le_bytes(*self.read(Self::DIFFICULTY_BITS_OFFSET..Self::DIFFICULTY_BITS_OFFSET + Self::DIFFICULTY_BITS_SIZE))
    }

}

impl<'a> BlockMut<'a> {

    #[inline]
    pub fn set_version(&mut self, version: u32) {
        write(&mut self.0, Block::VERSION_OFFSET..Block::VERSION_OFFSET + Block::VERSION_SIZE, &version.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_difficulty_bits(&mut self, exponent: u8, coefficient: u64) {
        assert!(exponent <= 114);
        assert_eq!(coefficient >> 56, 0);
        let bits = ((exponent as u64) << 56) | coefficient;
        write(&mut self.0, Block::DIFFICULTY_BITS_OFFSET..Block::DIFFICULTY_BITS_OFFSET + Block::DIFFICULTY_BITS_SIZE, &bits.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_timestamp(&mut self, timestamp: u128) {
        write(&mut self.0, Block::TIMESTAMP_OFFSET..Block::TIMESTAMP_OFFSET + Block::TIMESTAMP_SIZE, &timestamp.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_nonce(&mut self, nonce: u128) {
        write(&mut self.0, Block::NONCE_OFFSET..Block::NONCE_OFFSET + Block::NONCE_SIZE, &nonce.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_previous_challenge_block_hash(&mut self, previous_challenge_hash: &Sha512Hash) {
        previous_challenge_hash.0.to_little_endian(&mut self.0[Block::PREVIOUS_CHALLENGE_BLOCK_HASH_OFFSET..Block::PREVIOUS_CHALLENGE_BLOCK_HASH_OFFSET + Block::PREVIOUS_CHALLENGE_BLOCK_HASH_SIZE]);
    }

    #[inline]
    pub fn set_transaction_count(&mut self, transaction_count: u32) {
        write(&mut self.0, Block::TRANSACTION_COUNT_OFFSET..Block::TRANSACTION_COUNT_OFFSET + Block::TRANSACTION_COUNT_SIZE, &transaction_count.to_le_bytes()).unwrap();
    }

    #[inline]
    pub fn set_transactions(&mut self, transactions: &[u8]) {
        write1(&mut self.0, Block::TRANSACTIONS_OFFSET.., transactions).unwrap();
    }

    #[inline]
    pub fn hash(&self) -> Sha512Hash {
        Block(self.0).hash()
    }

    #[inline]
    pub fn difficulty_bits(&self) -> u64 {
        Block(self.0).difficulty_bits()
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
    pub fn set_root_block_hash(&mut self, hash: &Sha512Hash) {
        hash.0.to_little_endian(&mut self.0[BlockChallenge::ROOT_BLOCK_HASH_OFFSET..BlockChallenge::ROOT_BLOCK_HASH_OFFSET + BlockChallenge::ROOT_BLOCK_HASH_SIZE])
    }

    #[inline]
    pub fn set_challenge_block_hash(&mut self, hash: &Sha512Hash) {
        hash.0.to_little_endian(&mut self.0[BlockChallenge::CHALLENGE_BLOCK_HASH_OFFSET..BlockChallenge::CHALLENGE_BLOCK_HASH_OFFSET + BlockChallenge::CHALLENGE_BLOCK_HASH_SIZE])
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

struct Sha512Hash(U512);

impl Sha512Hash {
    
    pub const SIZE: usize = 64;
    
}

impl Rem<u64> for Sha512Hash {
    type Output = u64;

    fn rem(self, rhs: u64) -> Self::Output {
        (self.0 % rhs).as_u64()
    }
}


impl Display for Sha512Hash {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let mut buffer = vec![0u8;Sha512Hash::SIZE];
        self.0.to_big_endian(&mut buffer);
        write!(f, "{}", hex::encode(&buffer))
    } 
}

trait UTXODatabase {

}

trait Network {

    fn advertise(&self);
    fn register(&mut self, listener: impl Fn(Block));
}

trait Blockchain {

    type Error: Send;

    fn get(&self, index: u64) -> Result<Option<Vec<u8>>, Self::Error>;
    fn add(&mut self, block: Block) -> Result<(), Self::Error>;
    fn len(&self) -> u64;
}

fn mine_challenge<B>(new_block: &mut BlockMut, blockchain: &B) -> Result<Vec<u8>, B::Error> where B: Blockchain {
    let blockchain_len = blockchain.len();
    let nonce = rand::random();
    
    let mut challenge_buffer = vec![0u8;BlockChallenge::SIZE];
    let mut challenge = BlockChallengeMut(&mut challenge_buffer);

    // Hash new block
    new_block.set_nonce(nonce);
    let block_hash = new_block.hash();
    challenge.set_root_block_hash(&block_hash);
    
    // Retrieve the pair block (Disk/Ram operation)
    let block_index = block_hash % blockchain_len;
    let mut pair_block_buffer = blockchain.get(block_index)?.unwrap();
    let mut pair_block = BlockMut(&mut pair_block_buffer);
    pair_block.set_nonce(nonce);
    let pair_block_hash = pair_block.hash();
    
    // Write block challenge to block challenge index position
    challenge.set_challenge_block_hash(&pair_block_hash);
    Ok(challenge_buffer)
}

/// Returns a block-challenge with a hash that fulfills the difficulty
fn mine<B>(new_block_template: &Block, blockchain: &B) -> Result<(Sha512Hash, Vec<u8>, Vec<u8>), B::Error> where B: Blockchain + Sync{

    const AMOUNT_OF_THREADS: usize = 4;
    
    let should_exit = AtomicBool::new(false);
    thread::scope(|scope| {
        let mut handles = vec![];
        for _ in 0..AMOUNT_OF_THREADS {
            let mut block_buffer = new_block_template.0.to_vec();
            let thread_should_exit = &should_exit;
            handles.push(scope.spawn(move || {

                let mut thread_new_block = BlockMut(&mut block_buffer);
                while !thread_should_exit.load(atomic::Ordering::Acquire) {

                    let challenge_buffer = match mine_challenge(&mut thread_new_block, blockchain) {
                        Ok(res) => res,
                        Err(err) => {
                            thread_should_exit.store(true, atomic::Ordering::Release);
                            return Err(err);
                        },
                    };
                    let challenge_hash = BlockChallenge(&challenge_buffer).hash();

                    if fulfills_difficulty(&challenge_hash, thread_new_block.difficulty_bits()) {
                        println!("Found new block: {}", challenge_hash);
                        thread_should_exit.store(true, atomic::Ordering::Release);
                        return Ok(Some((challenge_hash, challenge_buffer, thread_new_block.0.to_vec())));
                    }
                }
                Ok(None)
            }));
        }
        for handle in handles {
            if let Some(res) = handle.join().unwrap()? {
                return Ok(res);
            }
        }
        unreachable!()
    })
}

fn address(public: &[u8; 2592]) -> Address {
    Address(RipeMd160Hash(hash_ripemd160(&hash_sha512_1(public))))
}

fn genesis_block(keys: &Keypair) -> Vec<u8> {
    let input_count = 0;
    let output_count = 1;
    let transaction_sizes = [(input_count, output_count)];
    let mut block_buffer = vec![0u8;Block::size(&transaction_sizes)];
    let mut transaction_buffer = vec![0u8;Transaction::size(input_count, output_count)];
    let mut transaction_output_buffer = vec![0u8;TransactionOutput::SIZE];

    let mut output = TransactionOutputMut(&mut transaction_output_buffer);
    output.set_amount(10000);
    output.set_receiver_address(&address(&keys.public));

    let mut transaction = TransactionMut(&mut transaction_buffer);
    transaction.set_owner(&keys.public);
    transaction.set_input_count(input_count as u32);
    transaction.set_output_count(output_count as u32);
    transaction.set_inputs_outputs(&[], &transaction_output_buffer);
    let transaction_hash = transaction.hash();
    let transaction_signature = keys.sign(&transaction_hash);
    transaction.set_signature(&transaction_signature);

    let mut block = BlockMut(&mut block_buffer);
    block.set_version(0);
    block.set_difficulty_bits(111, 0x00FFFFFFFFFFFFFF);
    block.set_timestamp(SystemTime::now().duration_since(SystemTime::UNIX_EPOCH).unwrap().as_millis());
    block.set_previous_challenge_block_hash(&Sha512Hash(U512::from(0)));
    block.set_nonce(0);
    block.set_transaction_count(1);
    block.set_transactions(&transaction_buffer);
    block_buffer
}

struct BlockchainStorage {
    tree: Db
}

impl BlockchainStorage {

    pub fn new(path: impl AsRef<std::path::Path>) -> sled::Result<Self> {
        let tree = sled::open(path)?;
        Ok(BlockchainStorage {
            tree,
        })
    }
}
impl Blockchain for BlockchainStorage {
    type Error = sled::Error;

    fn get(&self, index: u64) -> Result<Option<Vec<u8>>, Self::Error> {
        let x = self.tree.get(index.to_le_bytes())?;
        Ok(x.map(|x| x.to_vec()))
    }

    fn add(&mut self, block: Block) -> Result<(), Self::Error> {
        let len = self.len();
        self.tree.insert(len.to_le_bytes(), block.0).map(|_| ())
    }

    fn len(&self) -> u64 {
        self.tree.len() as u64
    }
}

#[derive(NetworkBehaviour)]
struct ThiumNetworkBehaviour {
    gossip_sub: gossipsub::Behaviour,
    mdns: mdns::tokio::Behaviour,
}

async fn network() -> Result<(), Box<dyn Error>> {
    let _ = tracing_subscriber::fmt()
        .with_env_filter(EnvFilter::from_default_env())
        .try_init();

    let mut swarm = libp2p::SwarmBuilder::with_new_identity()
        .with_tokio()
        .with_tcp(
            tcp::Config::default(),
            noise::Config::new,
            yamux::Config::default,
        )?
        .with_quic()
        .with_behaviour(|key| {
            // To content-address message, we can take the hash of message and use it as an ID.
            let message_id_fn = |message: &gossipsub::Message| {
                let mut s = DefaultHasher::new();
                message.data.hash(&mut s);
                gossipsub::MessageId::from(s.finish().to_string())
            };

            // Set a custom gossipsub configuration
            let gossipsub_config = gossipsub::ConfigBuilder::default()
                .heartbeat_interval(Duration::from_secs(10)) // This is set to aid debugging by not cluttering the log space
                .validation_mode(gossipsub::ValidationMode::Strict) // This sets the kind of message validation. The default is Strict (enforce message signing)
                .message_id_fn(message_id_fn) // content-address messages. No two messages of the same content will be propagated.
                .build()
                .map_err(|msg| io::Error::new(io::ErrorKind::Other, msg))?; // Temporary hack because `build` does not return a proper `std::error::Error`.

            // build a gossipsub network behaviour
            let gossipsub = gossipsub::Behaviour::new(
                gossipsub::MessageAuthenticity::Signed(key.clone()),
                gossipsub_config,
            )?;

            let mdns =
                mdns::tokio::Behaviour::new(mdns::Config::default(), key.public().to_peer_id())?;
            Ok(ThiumNetworkBehaviour { gossip_sub: gossipsub, mdns })
        })?
        .with_swarm_config(|c| c.with_idle_connection_timeout(Duration::from_secs(60)))
        .build();

    // Create a Gossipsub topic
    let topic = gossipsub::IdentTopic::new("test-net");
    // subscribes to our topic
    swarm.behaviour_mut().gossip_sub.subscribe(&topic)?;

    // Listen on all interfaces and whatever port the OS assigns
    swarm.listen_on("/ip4/0.0.0.0/udp/0/quic-v1".parse()?)?;
    swarm.listen_on("/ip4/0.0.0.0/tcp/0".parse()?)?;

    println!("Enter messages via STDIN and they will be sent to connected peers using Gossipsub");

    // Kick it off
    loop {
        select! {
            event = swarm.select_next_some() => match event {
                SwarmEvent::Behaviour(ThiumNetworkBehaviourEvent::Mdns(mdns::Event::Discovered(list))) => {
                    for (peer_id, _multiaddr) in list {
                        println!("mDNS discovered a new peer: {peer_id}");
                        swarm.behaviour_mut().gossip_sub.add_explicit_peer(&peer_id);
                    }
                },
                SwarmEvent::Behaviour(ThiumNetworkBehaviourEvent::Mdns(mdns::Event::Expired(list))) => {
                    for (peer_id, _multiaddr) in list {
                        println!("mDNS discover peer has expired: {peer_id}");
                        swarm.behaviour_mut().gossip_sub.remove_explicit_peer(&peer_id);
                    }
                },
                SwarmEvent::Behaviour(ThiumNetworkBehaviourEvent::GossipSub(gossipsub::Event::Message {
                    propagation_source: peer_id,
                    message_id: id,
                    message,
                })) => println!(
                        "Got message: '{}' with id: {id} from peer: {peer_id}",
                        String::from_utf8_lossy(&message.data),
                    ),
                SwarmEvent::NewListenAddr { address, .. } => {
                    println!("Local node is listening on {address}");
                }
                _ => {}
            }
        }
    }
}

fn main() {
    let keys = Keypair::generate();
    println!("Private: {} Public: {} Signature: {}", SECRETKEYBYTES, PUBLICKEYBYTES, SIGNBYTES);
    assert!(keys.public.len() == PUBLICKEYBYTES);
    assert!(keys.expose_secret().len() == SECRETKEYBYTES);


    let mut blockchain = BlockchainStorage::new("blockchain").unwrap();

    let mut genesis_block_buffer = genesis_block(&keys);
    let mut genesis_block = Block(&genesis_block_buffer);

    Blockchain::add(&mut blockchain, genesis_block).unwrap();

    let mut genesis_challenge_buffer = vec![0u8;BlockChallenge::SIZE];
    let mut genesis_challenge = BlockChallengeMut(&mut genesis_challenge_buffer);

    genesis_challenge.set_root_block_hash(&genesis_block.hash());
    genesis_challenge.set_challenge_block_hash(&Sha512Hash(U512::from(0)));
    let genesis_challenge_hash = genesis_challenge.hash();

    let mut next_block_buffer = genesis_block_buffer.clone();
    let mut next_block = BlockMut(&mut next_block_buffer);
    next_block.set_previous_challenge_block_hash(&genesis_challenge_hash);

    loop {
        let (challenge_hash, challenge_block, new_block) = mine(&Block(&next_block_buffer), &blockchain).unwrap();
        blockchain.add(Block(&new_block)).unwrap();
        genesis_block_buffer = new_block;
        genesis_block = Block(&genesis_block_buffer);
    }
}