//! Benchmarks for anubis_core cryptographic primitives.

use criterion::{black_box, criterion_group, criterion_main, BenchmarkId, Criterion, Throughput};

use anubis_core::aead::{ChaCha20Poly1305, KEY_SIZE, NONCE_SIZE, TAG_SIZE};
use anubis_core::kdf::HkdfShake256;
use anubis_core::keccak::sha3::sha3_256;
use anubis_core::keccak::shake::Shake256;
use anubis_core::merkle::MerkleTree;
use anubis_core::mldsa::{KeyPair, SEED_SIZE};
use anubis_core::mlkem::MlKemKeyPair;
use anubis_core::nonce::NonceDeriver;

fn sha3_256_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("SHA3-256");

    for size in [32, 64, 256, 1024, 4096, 16384].iter() {
        let input = vec![0u8; *size];
        group.throughput(Throughput::Bytes(*size as u64));
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, _| {
            b.iter(|| sha3_256(black_box(&input)))
        });
    }

    group.finish();
}

fn shake256_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("SHAKE256");

    let input = vec![0u8; 1024];
    for output_size in [32, 64, 128, 256].iter() {
        group.throughput(Throughput::Bytes(*output_size as u64));
        group.bench_with_input(
            BenchmarkId::new("squeeze", output_size),
            output_size,
            |b, &size| {
                b.iter(|| {
                    let mut shake = Shake256::new();
                    shake.absorb(black_box(&input));
                    let mut output = vec![0u8; size];
                    shake.squeeze(&mut output);
                    output
                })
            },
        );
    }

    group.finish();
}

fn chacha20poly1305_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("ChaCha20Poly1305");

    let key = [0u8; KEY_SIZE];
    let nonce = [0u8; NONCE_SIZE];
    let aad = [0u8; 16];
    let aead = ChaCha20Poly1305::new(&key).unwrap();

    for size in [64, 256, 1024, 4096].iter() {
        let plaintext = vec![0u8; *size];
        let mut ciphertext = vec![0u8; *size + TAG_SIZE];

        group.throughput(Throughput::Bytes(*size as u64));

        group.bench_with_input(BenchmarkId::new("encrypt", size), size, |b, _| {
            b.iter(|| {
                aead.seal(
                    black_box(&nonce),
                    black_box(&aad),
                    black_box(&plaintext),
                    black_box(&mut ciphertext),
                )
            })
        });
    }

    group.finish();
}

fn hkdf_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("HKDF-SHAKE256");

    let salt = [0u8; 32];
    let ikm = [0u8; 32];
    let info = b"benchmark";

    for output_size in [32, 64, 128].iter() {
        group.throughput(Throughput::Bytes(*output_size as u64));

        if *output_size == 32 {
            group.bench_function("derive-32", |b| {
                b.iter(|| {
                    HkdfShake256::derive::<32>(
                        black_box(&salt),
                        black_box(&ikm),
                        black_box(info),
                    )
                })
            });
        } else if *output_size == 64 {
            group.bench_function("derive-64", |b| {
                b.iter(|| {
                    HkdfShake256::derive::<64>(
                        black_box(&salt),
                        black_box(&ikm),
                        black_box(info),
                    )
                })
            });
        }
    }

    group.finish();
}

fn nonce_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Nonce-Derivation");

    let key = [0u8; 32];
    let deriver = NonceDeriver::new(key);

    group.bench_function("derive", |b| {
        let mut counter = 0u64;
        b.iter(|| {
            counter += 1;
            deriver.derive(black_box(counter), black_box(0), black_box(0x01))
        })
    });

    group.finish();
}

fn merkle_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("Merkle-Tree");

    for leaf_count in [4, 16, 64, 256].iter() {
        let leaves: Vec<[u8; 32]> = (0..*leaf_count).map(|i| [i as u8; 32]).collect();

        group.bench_with_input(
            BenchmarkId::new("build", leaf_count),
            &leaves,
            |b, leaves| {
                b.iter(|| {
                    let mut tree = MerkleTree::new();
                    for leaf in black_box(leaves) {
                        tree.add_leaf(leaf).unwrap();
                    }
                    tree.compute_root()
                })
            },
        );

        // Build tree for proof benchmark
        let mut tree = MerkleTree::new();
        for leaf in &leaves {
            tree.add_leaf(leaf).unwrap();
        }
        tree.compute_root().unwrap();

        group.bench_with_input(
            BenchmarkId::new("proof", leaf_count),
            &tree,
            |b, tree| {
                b.iter(|| tree.generate_proof(black_box(0)))
            },
        );
    }

    group.finish();
}

fn mldsa_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("ML-DSA-87");
    group.sample_size(10); // Reduce sample size due to slow operations

    let seed = [0u8; SEED_SIZE];
    let message = b"Benchmark message for ML-DSA-87 signature testing";

    group.bench_function("keygen", |b| {
        b.iter(|| KeyPair::from_seed(black_box(&seed)))
    });

    let keypair = KeyPair::from_seed(&seed).unwrap();

    group.bench_function("sign", |b| {
        b.iter(|| keypair.sign(black_box(message)))
    });

    let signature = keypair.sign(message).unwrap();

    group.bench_function("verify", |b| {
        b.iter(|| keypair.public_key().verify(black_box(message), black_box(&signature)))
    });

    group.finish();
}

fn mlkem_benchmark(c: &mut Criterion) {
    let mut group = c.benchmark_group("ML-KEM-1024");
    group.sample_size(10); // Reduce sample size due to slow operations

    group.bench_function("keygen", |b| {
        b.iter(|| MlKemKeyPair::generate())
    });

    let keypair = MlKemKeyPair::generate().unwrap();
    let pk = anubis_core::mlkem::MlKemPublicKey::from_bytes(keypair.public_key_bytes()).unwrap();

    group.bench_function("encapsulate", |b| {
        b.iter(|| pk.encapsulate())
    });

    let (ciphertext, _) = pk.encapsulate().unwrap();

    group.bench_function("decapsulate", |b| {
        b.iter(|| keypair.decapsulate(black_box(&ciphertext)))
    });

    group.finish();
}

criterion_group!(
    benches,
    sha3_256_benchmark,
    shake256_benchmark,
    chacha20poly1305_benchmark,
    hkdf_benchmark,
    nonce_benchmark,
    merkle_benchmark,
    mldsa_benchmark,
    mlkem_benchmark,
);

criterion_main!(benches);
