(** * Cryptographic Model for Anubis Notary

    This module provides the foundational abstract models for cryptographic
    primitives used in the Anubis Notary system. We define abstract types
    and axiomatized properties that capture the security guarantees of:

    - ML-DSA-87 digital signatures (FIPS 204)
    - ChaCha20Poly1305 authenticated encryption
    - SHA3-256 and SHAKE256 hash functions
    - Argon2id key derivation

    The proofs are structured to support RefinedRust verification, connecting
    high-level security properties to low-level implementation correctness.
*)

From Stdlib Require Import Lia ZArith List Strings.String.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Program.Equality.
From Stdlib Require Import Arith.Compare_dec.
From Stdlib Require Import Bool.Bool.
Import ListNotations.

Open Scope Z_scope.

(** ** Byte and Word Representations *)

(** A byte is represented as an integer in range [0, 255] *)
Definition byte := { n : Z | 0 <= n < 256 }.

(** Convert a byte to its underlying integer *)
Definition byte_to_Z (b : byte) : Z := proj1_sig b.

(** Create a byte from an integer with proof of range *)
Program Definition Z_to_byte (n : Z) (H : 0 <= n < 256) : byte := exist _ n H.

(** Bytes list represents a byte string *)
Definition bytes := list byte.

(** Length of a byte string *)
Definition bytes_len (bs : bytes) : nat := List.length bs.

(** Byte equality - uses Z.eqb on the underlying values *)
Definition byte_eqb (b1 b2 : byte) : bool :=
  Z.eqb (byte_to_Z b1) (byte_to_Z b2).

(** Bytes list equality *)
Fixpoint bytes_eqb (bs1 bs2 : bytes) : bool :=
  match bs1, bs2 with
  | nil, nil => true
  | b1 :: rest1, b2 :: rest2 => andb (byte_eqb b1 b2) (bytes_eqb rest1 rest2)
  | _, _ => false
  end.

(** ** Constant-Time Operations Model *)

(** Abstract predicate for timing-independent computation.
    A function is timing-independent if its execution time depends
    only on public parameters (lengths), not on secret values. *)
Parameter timing_independent : forall {A B : Type}, (A -> B) -> Prop.

(** Axiom: Composition preserves timing independence *)
Axiom timing_independent_compose :
  forall {A B C : Type} (f : A -> B) (g : B -> C),
    timing_independent f ->
    timing_independent g ->
    timing_independent (fun x => g (f x)).

(** Axiom: XOR is timing-independent *)
Axiom timing_independent_xor :
  forall (n : nat),
    timing_independent (fun p : bytes * bytes =>
      let (a, b) := p in
      match Nat.eqb (List.length a) (List.length b) with
      | true => Some (combine a b)
      | false => None
      end).

(** ** Abstract Hash Function Model *)

Module Type HASH_FUNCTION.
  (** Abstract hash state *)
  Parameter state : Type.

  (** Initial state *)
  Parameter init : state.

  (** Absorb bytes into state *)
  Parameter absorb : state -> bytes -> state.

  (** Squeeze n bytes from state *)
  Parameter squeeze : state -> nat -> bytes.

  (** Fixed-output hash *)
  Parameter hash : bytes -> nat -> bytes.

  (** Note: Determinism is inherent in Coq's functional model.
      The function [hash] is pure and total - same inputs always yield
      same outputs. No axiom needed; this is guaranteed by construction.

      For cryptographic purposes, this models an idealized hash function
      without internal state or randomness. *)

  (** Axiom: Output length is exactly n *)
  Axiom hash_length :
    forall (input : bytes) (n : nat),
      bytes_len (hash input n) = n.

  (** Axiom: Collision resistance (computational assumption) *)
  Parameter collision_resistant : Prop.

  (** Axiom: Preimage resistance (computational assumption) *)
  Parameter preimage_resistant : Prop.

  (** Axiom: Second preimage resistance *)
  Parameter second_preimage_resistant : Prop.
End HASH_FUNCTION.

(** ** SHA3-256 Instantiation *)

Module SHA3_256 <: HASH_FUNCTION.
  (** Keccak state: 5x5 matrix of 64-bit words *)
  Definition lane := Z.  (* 64-bit word *)
  Definition state_array := list (list lane).
  Definition state := state_array.

  (** Initial state (all zeros) *)
  Definition init : state :=
    repeat (repeat 0 5) 5.

  (** Rate for SHA3-256: 1088 bits = 136 bytes *)
  Definition rate_bytes : nat := 136.

  (** Output size: 256 bits = 32 bytes *)
  Definition output_bytes : nat := 32.

  (** Abstract absorb operation *)
  Parameter absorb : state -> bytes -> state.

  (** Abstract squeeze operation *)
  Parameter squeeze : state -> nat -> bytes.

  (** Fixed 32-byte hash *)
  Definition hash (input : bytes) (n : nat) : bytes :=
    squeeze (absorb init input) n.

  (** SHA3-256 specific hash function *)
  Definition sha3_256 (input : bytes) : bytes :=
    hash input output_bytes.

  (** Note: hash is deterministic by construction - it's a pure Coq function. *)

  Axiom hash_length :
    forall (input : bytes) (n : nat),
      bytes_len (hash input n) = n.

  (** Security assumptions *)
  Parameter collision_resistant : Prop.
  Parameter preimage_resistant : Prop.
  Parameter second_preimage_resistant : Prop.

  (** SHA3-256 is a random oracle in the ideal model *)
  Parameter random_oracle_model : Prop.
End SHA3_256.

(** ** SHAKE256 XOF Instantiation *)

Module SHAKE256.
  Definition state := SHA3_256.state.
  Definition init := SHA3_256.init.

  (** Rate for SHAKE256: 1088 bits = 136 bytes *)
  Definition rate_bytes : nat := 136.

  (** SHAKE256 can produce arbitrary List.length output *)
  Parameter absorb : state -> bytes -> state.
  Parameter squeeze : state -> nat -> bytes.

  (** XOF operation: hash input to arbitrary List.length *)
  Definition xof (input : bytes) (output_len : nat) : bytes :=
    squeeze (absorb init input) output_len.

  Axiom xof_deterministic :
    forall (input : bytes) (n : nat),
      xof input n = xof input n.

  Axiom xof_length :
    forall (input : bytes) (n : nat),
      bytes_len (xof input n) = n.

  (** XOF output is indistinguishable from random *)
  Parameter xof_indistinguishable_from_random : Prop.
End SHAKE256.

(** ** Digital Signature Model *)

Module Type SIGNATURE_SCHEME.
  (** Key types *)
  Parameter secret_key : Type.
  Parameter public_key : Type.
  Parameter signature : Type.

  (** Key generation from seed *)
  Parameter keygen : bytes -> secret_key * public_key.

  (** Sign a message *)
  Parameter sign : secret_key -> bytes -> signature.

  (** Verify a signature *)
  Parameter verify : public_key -> bytes -> signature -> bool.

  (** Signature to bytes *)
  Parameter sig_to_bytes : signature -> bytes.
  Parameter bytes_to_sig : bytes -> option signature.

  (** Public key to bytes *)
  Parameter pk_to_bytes : public_key -> bytes.
  Parameter bytes_to_pk : bytes -> option public_key.

  (** Correctness: valid signatures verify *)
  Axiom sign_verify_correct :
    forall (seed : bytes) (msg : bytes),
      let (sk, pk) := keygen seed in
      verify pk msg (sign sk msg) = true.

  (** Note: Determinism is inherent in Coq's functional model.
      The function [keygen] is pure - same seed always yields same keypair.
      No axiom needed; this is guaranteed by construction.

      This models deterministic key generation from a seed (as in FIPS 204),
      not randomized keygen which would require a different model. *)

  (** EUF-CMA security (existential unforgeability under chosen message attack) *)
  Parameter euf_cma_secure : Prop.
End SIGNATURE_SCHEME.

(** ** ML-DSA-87 Instantiation (FIPS 204) *)

Module MLDSA87 <: SIGNATURE_SCHEME.
  (** ML-DSA-87 parameter set *)
  Definition security_level : nat := 5.  (* NIST Level 5 *)
  Definition n : nat := 256.             (* Polynomial degree *)
  Definition k : nat := 8.               (* Matrix rows *)
  Definition l : nat := 7.               (* Matrix columns *)
  Definition q : Z := 8380417.           (* Modulus *)

  (** Key sizes *)
  Definition seed_size : nat := 32.
  Definition sk_size : nat := 4896.
  Definition pk_size : nat := 2592.
  Definition sig_size : nat := 4627.

  (** Abstract key types *)
  Definition secret_key := bytes.
  Definition public_key := bytes.
  Definition signature := bytes.

  (** Key generation from 32-byte seed *)
  Parameter keygen : bytes -> secret_key * public_key.

  (** Signing operation (hedged, uses internal randomness) *)
  Parameter sign : secret_key -> bytes -> signature.

  (** Verification operation *)
  Parameter verify : public_key -> bytes -> signature -> bool.

  (** Serialization *)
  Definition sig_to_bytes (s : signature) : bytes := s.

  Definition bytes_to_sig (bs : bytes) : option signature :=
    if Nat.eqb (bytes_len bs) sig_size then Some bs else None.

  Definition pk_to_bytes (pk : public_key) : bytes := pk.

  Definition bytes_to_pk (bs : bytes) : option public_key :=
    if Nat.eqb (bytes_len bs) pk_size then Some bs else None.

  (** Correctness theorem *)
  Axiom sign_verify_correct :
    forall (seed : bytes) (msg : bytes),
      let (sk, pk) := keygen seed in
      verify pk msg (sign sk msg) = true.

  (** Note: keygen is deterministic by construction - it's a pure Coq function.
      Same seed always produces same keypair. *)

  (** Key size invariants *)
  Axiom keygen_sizes :
    forall (seed : bytes),
      bytes_len seed = seed_size ->
      let (sk, pk) := keygen seed in
      bytes_len sk = sk_size /\ bytes_len pk = pk_size.

  (** Signature size invariant *)
  Axiom sign_size :
    forall (sk : secret_key) (msg : bytes),
      bytes_len (sign sk msg) = sig_size.

  (** EUF-CMA security under Module-LWE assumption *)
  Parameter euf_cma_secure : Prop.

  (** Post-quantum security *)
  Parameter pq_secure : Prop.

  (** ML-DSA-87 provides NIST Level 5 security *)
  Axiom security_level_5 :
    pq_secure.

  (** EUF-CMA implies: signing msg1 produces a signature that does not
      verify for any different msg2. This is the core security property
      that prevents existential forgery.

      Reference: Goldwasser, Micali, Rivest "A Digital Signature Scheme
      Secure Against Adaptive Chosen-Message Attacks" (1988), Def. 3 *)
  Axiom euf_cma_different_message :
    forall (seed : bytes) (pk : public_key) (msg1 msg2 : bytes),
      euf_cma_secure ->
      pk = snd (keygen seed) ->
      msg1 <> msg2 ->
      verify pk msg2 (sign (fst (keygen seed)) msg1) = false.
End MLDSA87.

(** ** AEAD Model *)

Module Type AEAD_SCHEME.
  (** Types *)
  Parameter key : Type.
  Parameter nonce : Type.
  Parameter tag : Type.

  (** Key/nonce sizes *)
  Parameter key_size : nat.
  Parameter nonce_size : nat.
  Parameter tag_size : nat.

  (** Encryption: plaintext + AAD -> ciphertext + tag *)
  Parameter encrypt : key -> nonce -> bytes -> bytes -> bytes * tag.

  (** Decryption: ciphertext + tag + AAD -> plaintext or failure *)
  Parameter decrypt : key -> nonce -> bytes -> tag -> bytes -> option bytes.

  (** Correctness: decryption inverts encryption *)
  Axiom encrypt_decrypt_correct :
    forall (k : key) (n : nonce) (pt aad : bytes),
      let (ct, t) := encrypt k n pt aad in
      decrypt k n ct t aad = Some pt.

  (** IND-CPA security (indistinguishability under chosen plaintext attack) *)
  Parameter ind_cpa_secure : Prop.

  (** INT-CTXT security (integrity of ciphertext) *)
  Parameter int_ctxt_secure : Prop.
End AEAD_SCHEME.

(** ** ChaCha20-Poly1305 Instantiation *)

Module ChaCha20Poly1305 <: AEAD_SCHEME.
  Definition key_size : nat := 32.
  Definition nonce_size : nat := 12.
  Definition tag_size : nat := 16.

  Definition key := bytes.
  Definition nonce := bytes.
  Definition tag := bytes.

  (** ChaCha20 stream cipher *)
  Parameter chacha20_block : key -> nonce -> Z -> bytes.
  Parameter chacha20_encrypt : key -> nonce -> bytes -> bytes.

  (** Poly1305 MAC *)
  Parameter poly1305 : bytes -> bytes -> tag.

  (** AEAD construction *)
  Parameter encrypt : key -> nonce -> bytes -> bytes -> bytes * tag.
  Parameter decrypt : key -> nonce -> bytes -> tag -> bytes -> option bytes.

  Axiom encrypt_decrypt_correct :
    forall (k : key) (n : nonce) (pt aad : bytes),
      let (ct, t) := encrypt k n pt aad in
      decrypt k n ct t aad = Some pt.

  (** Ciphertext List.length equals plaintext List.length *)
  Axiom encrypt_length :
    forall (k : key) (n : nonce) (pt aad : bytes),
      let (ct, _) := encrypt k n pt aad in
      bytes_len ct = bytes_len pt.

  (** Security properties *)
  Parameter ind_cpa_secure : Prop.
  Parameter int_ctxt_secure : Prop.

  (** ChaCha20-Poly1305 is IND-CCA2 secure *)
  Axiom ind_cca2_secure :
    ind_cpa_secure /\ int_ctxt_secure.

  (** Nonce misuse detection *)
  Axiom nonce_misuse_detectable :
    forall (k : key) (n : nonce) (pt1 pt2 aad : bytes),
      pt1 <> pt2 ->
      let (ct1, t1) := encrypt k n pt1 aad in
      let (ct2, t2) := encrypt k n pt2 aad in
      ct1 <> ct2.
End ChaCha20Poly1305.

(** ** Key Derivation Function Model *)

Module Type KDF.
  (** Parameters *)
  Parameter min_salt_len : nat.
  Parameter min_output_len : nat.
  Parameter max_output_len : nat.

  (** Key derivation operation *)
  Parameter derive : bytes -> bytes -> bytes -> nat -> bytes.

  (** Output List.length is exact *)
  Axiom derive_length :
    forall (password salt info : bytes) (len : nat),
      (len <= max_output_len)%nat ->
      bytes_len (derive password salt info len) = len.

  (** Determinism *)
  Axiom derive_deterministic :
    forall (password salt info : bytes) (len : nat),
      derive password salt info len = derive password salt info len.

  (** Key derivation security *)
  Parameter kdf_secure : Prop.
End KDF.

(** ** Argon2id Instantiation *)

Module Argon2id.
  (** Version *)
  Definition version : Z := 19.  (* 0x13 *)
  Definition variant : Z := 2.   (* Argon2id *)

  (** Parameter constraints from CLAUDE.md *)
  (** Note: Using Z for large values to avoid Rocq 9.0 nat stack issues *)
  Definition min_m_cost_kib : Z := 524288.   (* 512 MiB minimum - matches ARGON2ID_LOW_M_COST *)
  Definition default_m_cost_kib : Z := 4194304.  (* 4 GiB default *)
  Definition min_t_cost : Z := 3.
  Definition min_parallelism : Z := 1.

  (** Block size: 1 KiB = 1024 bytes = 128 x 64-bit words *)
  Definition block_size_bytes : nat := 1024.
  Definition block_words : nat := 128.

  Record params := mk_params {
    m_cost : Z;        (* Memory in KiB *)
    t_cost : Z;        (* Time/iterations *)
    p_lanes : Z;       (* Parallelism *)
    tag_len : nat;     (* Output length *)
  }.

  (** Valid parameters predicate *)
  Definition valid_params (p : params) : Prop :=
    m_cost p >= min_m_cost_kib /\
    t_cost p >= min_t_cost /\
    p_lanes p >= min_parallelism /\
    (tag_len p > 0)%nat /\ (tag_len p <= 4096)%nat.

  (** Low-memory mode parameters *)
  Definition low_memory_params : params := {|
    m_cost := min_m_cost_kib;
    t_cost := 4;  (* Extra iteration to compensate *)
    p_lanes := 1;
    tag_len := 32;
  |}.

  (** Default (high-security) parameters *)
  Definition default_params : params := {|
    m_cost := default_m_cost_kib;
    t_cost := min_t_cost;
    p_lanes := 1;
    tag_len := 32;
  |}.

  Lemma low_memory_params_valid : valid_params low_memory_params.
  Proof.
    unfold valid_params, low_memory_params, min_m_cost_kib, min_t_cost, min_parallelism.
    simpl.
    repeat split; try lia; auto with arith.
  Qed.

  Lemma default_params_valid : valid_params default_params.
  Proof.
    unfold valid_params, default_params, default_m_cost_kib, min_m_cost_kib, min_t_cost, min_parallelism.
    simpl.
    repeat split; try lia; auto with arith.
  Qed.

  (** H0 initial hash computation *)
  Parameter compute_H0 : params -> bytes -> bytes -> bytes -> bytes -> bytes.

  (** H' variable-List.length hash *)
  Parameter H_prime : bytes -> nat -> bytes.

  (** Axiom: H' output List.length is exact *)
  Axiom H_prime_length :
    forall (input : bytes) (len : nat),
      (len > 0)%nat ->
      bytes_len (H_prime input len) = len.

  (** G compression function *)
  Parameter G : bytes -> bytes -> bytes.

  (** Axiom: G output is one block *)
  Axiom G_block_size :
    forall (x y : bytes),
      bytes_len x = block_size_bytes ->
      bytes_len y = block_size_bytes ->
      bytes_len (G x y) = block_size_bytes.

  (** Full Argon2id derivation *)
  Parameter argon2id : params -> bytes -> bytes -> bytes.

  (** Axiom: Output List.length matches tag_len *)
  Axiom argon2id_length :
    forall (p : params) (password salt : bytes),
      valid_params p ->
      bytes_len (argon2id p password salt) = tag_len p.

  (** Argon2id is memory-hard *)
  Parameter memory_hard : params -> Prop.

  (** Security: Argon2id resists time-memory tradeoffs *)
  Axiom memory_hardness_security :
    forall (p : params),
      valid_params p ->
      memory_hard p.
End Argon2id.

(** ** Domain Separation *)

Module DomainSeparation.
  (** Domain separation prefixes for different operations.
      Each domain is a distinct ASCII byte sequence to ensure
      cryptographic domain separation. *)

  (** Helper: convert Z to byte with automatic range proof (for ASCII values) *)
  Local Program Definition ascii_byte (n : Z) (H : 0 <= n < 256) : byte :=
    exist _ n H.

  (** Helper notation for creating bytes - proves range automatically *)
  Local Ltac make_byte n := exact (exist _ n ltac:(lia)).

  (** "anubis-notary:sign:v1:" as ASCII bytes - length 22 *)
  (** Distinguishing byte at position 14: 's' = 115 *)
  Definition sign_domain : bytes.
    refine [exist _ 97 _; exist _ 110 _; exist _ 117 _; exist _ 98 _;
            exist _ 105 _; exist _ 115 _; exist _ 45 _; exist _ 110 _;
            exist _ 111 _; exist _ 116 _; exist _ 97 _; exist _ 114 _;
            exist _ 121 _; exist _ 58 _;
            exist _ 115 _; exist _ 105 _; exist _ 103 _; exist _ 110 _; exist _ 58 _;
            exist _ 118 _; exist _ 49 _; exist _ 58 _]; lia.
  Defined.

  (** "anubis-notary:attest:v1:" as ASCII bytes - length 24 *)
  (** Distinguishing byte at position 14: 'a' = 97 *)
  Definition attest_domain : bytes.
    refine [exist _ 97 _; exist _ 110 _; exist _ 117 _; exist _ 98 _;
            exist _ 105 _; exist _ 115 _; exist _ 45 _; exist _ 110 _;
            exist _ 111 _; exist _ 116 _; exist _ 97 _; exist _ 114 _;
            exist _ 121 _; exist _ 58 _;
            exist _ 97 _; exist _ 116 _; exist _ 116 _; exist _ 101 _;
            exist _ 115 _; exist _ 116 _; exist _ 58 _;
            exist _ 118 _; exist _ 49 _; exist _ 58 _]; lia.
  Defined.

  (** "anubis-notary:license:v1:" as ASCII bytes - length 26 *)
  (** Distinguishing byte at position 14: 'l' = 108 *)
  Definition license_domain : bytes.
    refine [exist _ 97 _; exist _ 110 _; exist _ 117 _; exist _ 98 _;
            exist _ 105 _; exist _ 115 _; exist _ 45 _; exist _ 110 _;
            exist _ 111 _; exist _ 116 _; exist _ 97 _; exist _ 114 _;
            exist _ 121 _; exist _ 58 _;
            exist _ 108 _; exist _ 105 _; exist _ 99 _; exist _ 101 _;
            exist _ 110 _; exist _ 115 _; exist _ 101 _; exist _ 58 _;
            exist _ 118 _; exist _ 49 _; exist _ 58 _]; lia.
  Defined.

  (** "anubis-notary:key-rotation:v1:" as ASCII bytes - length 31 *)
  (** Distinguishing byte at position 14: 'k' = 107 *)
  Definition rotation_domain : bytes.
    refine [exist _ 97 _; exist _ 110 _; exist _ 117 _; exist _ 98 _;
            exist _ 105 _; exist _ 115 _; exist _ 45 _; exist _ 110 _;
            exist _ 111 _; exist _ 116 _; exist _ 97 _; exist _ 114 _;
            exist _ 121 _; exist _ 58 _;
            exist _ 107 _; exist _ 101 _; exist _ 121 _; exist _ 45 _;
            exist _ 114 _; exist _ 111 _; exist _ 116 _; exist _ 97 _;
            exist _ 116 _; exist _ 105 _; exist _ 111 _; exist _ 110 _; exist _ 58 _;
            exist _ 118 _; exist _ 49 _; exist _ 58 _]; lia.
  Defined.

  (** Domain separation ensures different operations don't collide *)
  Definition domain_separated (d1 d2 : bytes) : Prop :=
    d1 <> d2.

  (** All domains are pairwise distinct - now provable with concrete definitions *)
  Theorem domains_distinct :
    domain_separated sign_domain attest_domain /\
    domain_separated sign_domain license_domain /\
    domain_separated sign_domain rotation_domain /\
    domain_separated attest_domain license_domain /\
    domain_separated attest_domain rotation_domain /\
    domain_separated license_domain rotation_domain.
  Proof.
    unfold domain_separated, sign_domain, attest_domain, license_domain, rotation_domain.
    repeat split; intro H; discriminate H.
  Qed.

  (** Prepend domain to message *)
  Definition with_domain (domain msg : bytes) : bytes :=
    domain ++ msg.

  (** Helper: if d1 ++ m1 = d2 ++ m2 and |d1| = |d2|, then d1 = d2 *)
  Lemma app_same_length_prefix :
    forall (A : Type) (d1 d2 m1 m2 : list A),
      List.length d1 = List.length d2 ->
      d1 ++ m1 = d2 ++ m2 ->
      d1 = d2.
  Proof.
    intros A d1.
    induction d1 as [| x1 d1' IH].
    - intros d2 m1 m2 Hlen Heq.
      destruct d2; [reflexivity | simpl in Hlen; discriminate].
    - intros d2 m1 m2 Hlen Heq.
      destruct d2 as [| x2 d2'].
      + simpl in Hlen. discriminate.
      + simpl in Hlen. injection Hlen as Hlen'.
        simpl in Heq. injection Heq as Hx Htail.
        subst x2.
        f_equal.
        apply IH with m1 m2; assumption.
  Qed.

  (** Helper: prefix uniqueness for same-List.length lists *)
  Lemma prefix_unique_same_length :
    forall (A : Type) (d1 d2 m1 m2 : list A),
      List.length d1 = List.length d2 ->
      d1 <> d2 ->
      d1 ++ m1 <> d2 ++ m2.
  Proof.
    intros A d1 d2 m1 m2 Hlen Hne Heq.
    apply Hne.
    eapply app_same_length_prefix; eassumption.
  Qed.

  (** Domain separation prevents cross-protocol attacks *)
  (** Assuming domain prefixes have the same List.length (which they do in practice) *)
  Theorem domain_separation_security :
    forall (d1 d2 : bytes) (m1 m2 : bytes),
      List.length d1 = List.length d2 ->
      domain_separated d1 d2 ->
      with_domain d1 m1 <> with_domain d2 m2.
  Proof.
    intros d1 d2 m1 m2 Hlen Hsep.
    unfold with_domain.
    apply prefix_unique_same_length.
    - exact Hlen.
    - unfold domain_separated in Hsep. exact Hsep.
  Qed.

  (** with_domain is injective in the message argument for a fixed domain *)
  Lemma with_domain_injective :
    forall (d m1 m2 : bytes),
      m1 <> m2 ->
      with_domain d m1 <> with_domain d m2.
  Proof.
    intros d m1 m2 Hne Heq.
    unfold with_domain in Heq.
    apply app_inv_head in Heq.
    contradiction.
  Qed.
End DomainSeparation.

(** ** Zeroization Model *)

(** This module provides both abstract and concrete models for zeroization.

    IMPLEMENTATION LINK TO RUST:
    The Rust implementation uses the `zeroize` crate which provides:
    - `Zeroizing<T>`: A wrapper that zeroizes on drop
    - `Zeroize` trait: Provides `zeroize(&mut self)` method
    - `volatile_set_memory`: Uses `write_volatile` to prevent optimization
    - `compiler_fence(Ordering::SeqCst)`: Memory barrier after zeroization

    The connection is:
    1. `zeroize_bytes` in Coq ≈ `slice.zeroize()` in Rust
    2. `all_bytes_zero` in Coq ≈ `slice.iter().all(|&b| b == 0)` in Rust
    3. `volatile_zeroize` in Coq ≈ `volatile_set_memory` + `compiler_fence` in Rust

    VERIFICATION STATUS:
    - Byte-level correctness: PROVEN (zeroize_bytes_correct)
    - Dead-store elimination resistance: AXIOMATIZED (volatile semantics)
    - Drop guarantee: Relies on Rust's Drop trait semantics *)

Module Zeroization.
  (** === Concrete Byte-Level Model === *)

  (** A secret buffer is a list of bytes with a known length *)
  Definition secret_buffer := bytes.

  (** Zeroize a buffer by replacing all bytes with zero *)
  Program Definition zero_byte : byte := exist _ 0 _.
  Next Obligation. lia. Qed.

  Definition zeroize_bytes (buf : secret_buffer) : secret_buffer :=
    repeat zero_byte (List.length buf).

  (** Predicate: all bytes in buffer are zero *)
  Definition all_bytes_zero (buf : secret_buffer) : Prop :=
    Forall (fun b => proj1_sig b = 0) buf.

  (** Helper: Forall on repeat *)
  Lemma Forall_repeat : forall {A} (P : A -> Prop) (x : A) (n : nat),
    P x -> Forall P (repeat x n).
  Proof.
    intros A P x n Hx.
    induction n; simpl; constructor; assumption.
  Qed.

  (** THEOREM: zeroize_bytes produces all-zero buffer *)
  Theorem zeroize_bytes_correct :
    forall (buf : secret_buffer),
      all_bytes_zero (zeroize_bytes buf).
  Proof.
    intros buf.
    unfold zeroize_bytes, all_bytes_zero.
    apply Forall_repeat.
    simpl. reflexivity.
  Qed.

  (** THEOREM: zeroize_bytes preserves length *)
  Theorem zeroize_bytes_length :
    forall (buf : secret_buffer),
      List.length (zeroize_bytes buf) = List.length buf.
  Proof.
    intros buf.
    unfold zeroize_bytes.
    apply repeat_length.
  Qed.

  (** === Abstract Memory Model (for separation logic) === *)

  (** Abstract memory location *)
  Parameter mem_loc : Type.

  (** Zeroization operation at abstract location *)
  Parameter zeroize : mem_loc -> Prop.

  (** Predicate: all bytes at location are zero *)
  Parameter all_zero : mem_loc -> Prop.

  (** Zeroization achieves all-zero state *)
  Axiom zeroize_correct :
    forall (loc : mem_loc),
      zeroize loc -> all_zero loc.

  (** === Volatile Write Model (dead-store elimination resistance) === *)

  (** Volatile zeroization uses write_volatile semantics:
      - Each byte write is observable
      - Compiler cannot reorder or eliminate writes
      - Memory fence ensures visibility to other threads *)
  Parameter volatile_zeroize : mem_loc -> Prop.

  (** AXIOM: Volatile writes are not eliminated by the compiler.

      JUSTIFICATION: The Rust `zeroize` crate implementation:
      ```rust
      pub fn zeroize_flat_type<Z: Zeroize + ?Sized>(z: &mut Z) {
          unsafe {
              let ptr = z as *mut Z as *mut u8;
              let len = core::mem::size_of_val(z);
              core::ptr::write_volatile(ptr, 0u8);
              // ...repeat for all bytes...
          }
          core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
      }
      ```

      The `write_volatile` function has defined semantics in Rust/LLVM:
      - Volatile accesses are never optimized away
      - They are not reordered with respect to other volatile accesses

      The `compiler_fence` ensures the writes are complete before
      the function returns. *)
  Axiom volatile_zeroize_not_eliminated :
    forall (loc : mem_loc),
      volatile_zeroize loc -> zeroize loc.

  (** === Zeroizing<T> Wrapper Model === *)

  (** Model of Rust's Zeroizing<T> wrapper that zeroizes on drop.

      In Rust:
      ```rust
      pub struct Zeroizing<Z: Zeroize>(Z);

      impl<Z: Zeroize> Drop for Zeroizing<Z> {
          fn drop(&mut self) {
              self.0.zeroize();
          }
      }
      ```

      Key properties:
      1. The inner value is always zeroized when Zeroizing<T> goes out of scope
      2. This happens even on panic (guaranteed by Rust's drop semantics)
      3. The zeroization is volatile (not eliminated) *)

  (** State of a Zeroizing<T> wrapper *)
  Inductive zeroizing_state :=
    | ZLive : secret_buffer -> zeroizing_state  (* Contains secret data *)
    | ZDropped : zeroizing_state.               (* Has been dropped and zeroized *)

  (** Drop operation on Zeroizing<T> *)
  Definition zeroizing_drop (s : zeroizing_state) : zeroizing_state * secret_buffer :=
    match s with
    | ZLive buf => (ZDropped, zeroize_bytes buf)
    | ZDropped => (ZDropped, [])  (* Already dropped - no-op *)
    end.

  (** THEOREM: After drop, the buffer is zeroized *)
  Theorem zeroizing_drop_zeroizes :
    forall (buf : secret_buffer),
      let (_, final_buf) := zeroizing_drop (ZLive buf) in
      all_bytes_zero final_buf.
  Proof.
    intros buf.
    simpl.
    apply zeroize_bytes_correct.
  Qed.

  (** === Scope-Based Zeroization === *)

  (** Model of scope-based secret handling:
      ```rust
      {
          let secret = Zeroizing::new(key_bytes);
          // ... use secret ...
      } // secret.zeroize() called here automatically
      ```

      The Coq model captures this as a bracket operation. *)

  Definition with_secret {A : Type} (secret : secret_buffer) (f : secret_buffer -> A) : A * secret_buffer :=
    let result := f secret in
    let zeroized := zeroize_bytes secret in
    (result, zeroized).

  (** THEOREM: with_secret always produces zeroized buffer *)
  Theorem with_secret_zeroizes :
    forall {A : Type} (secret : secret_buffer) (f : secret_buffer -> A),
      let (_, final) := with_secret secret f in
      all_bytes_zero final.
  Proof.
    intros A secret f.
    unfold with_secret.
    apply zeroize_bytes_correct.
  Qed.

End Zeroization.

(** ** Nonce Management *)

Module NonceManagement.
  Definition nonce_size : nat := 12.

  (** Nonce state: counter or random *)
  Inductive nonce_source :=
    | Counter : Z -> nonce_source
    | Random : nonce_source.

  (** Zero byte for placeholder nonces *)
  Program Definition zero_byte : byte := exist _ 0 _.
  Next Obligation. lia. Qed.

  (** Helper to create a byte from Z (clamped to 0-255) *)
  Program Definition byte_of_Z (z : Z) : byte := exist _ (z mod 256) _.
  Next Obligation. apply Z.mod_pos_bound. lia. Qed.

  (** Convert counter value to nonce bytes (little-endian encoding) *)
  (** 12-byte nonce: first 8 bytes are LE-encoded counter, last 4 are zero *)
  Fixpoint Z_to_le_bytes_aux (n : nat) (z : Z) : bytes :=
    match n with
    | O => []
    | S n' => byte_of_Z z :: Z_to_le_bytes_aux n' (z / 256)
    end.

  Definition counter_to_nonce (n : Z) : bytes :=
    (* 8 bytes for counter, 4 bytes padding *)
    Z_to_le_bytes_aux 8 n ++ repeat zero_byte 4.

  (** Generate next nonce *)
  (** For Counter mode: derives nonce deterministically from counter value
      For Random mode: would use CSPRNG (axiomatized as it requires external state) *)
  Definition next_nonce (src : nonce_source) : bytes * nonce_source :=
    match src with
    | Counter n => (counter_to_nonce n, Counter (n + 1))
    | Random => (repeat zero_byte nonce_size, Random)  (* Axiomatized: requires CSPRNG *)
    end.

  (** LE encoding is injective: different values produce different byte sequences *)
  Lemma Z_to_le_bytes_aux_injective :
    forall k z1 z2,
      0 <= z1 < Z.pow 2 (Z.of_nat k * 8) ->
      0 <= z2 < Z.pow 2 (Z.of_nat k * 8) ->
      Z_to_le_bytes_aux k z1 = Z_to_le_bytes_aux k z2 ->
      z1 = z2.
  Proof.
    induction k; intros z1 z2 H1 H2 Heq.
    - (* k = 0 *)
      simpl in H1, H2. lia.
    - (* k = S k' *)
      simpl in Heq.
      injection Heq as Hbyte Htail.
      (* First bytes equal means z1 mod 256 = z2 mod 256 *)
      unfold byte_of_Z in Hbyte.
      assert (Hmod: z1 mod 256 = z2 mod 256).
      { inversion Hbyte. reflexivity. }
      (* Tail equal means z1/256 = z2/256 (by IH) *)
      assert (Hdiv: z1 / 256 = z2 / 256).
      { apply IHk.
        - split; [apply Z.div_pos; lia |].
          apply Z.div_lt_upper_bound; [lia |].
          (* 0 <= z1 < 2^(8*(S k)) implies z1/256 < 2^(8*k) *)
          assert (Hpow: Z.pow 2 (Z.of_nat (S k) * 8) = 256 * Z.pow 2 (Z.of_nat k * 8)).
          { rewrite Nat2Z.inj_succ.
            replace (Z.succ (Z.of_nat k) * 8) with (Z.of_nat k * 8 + 8) by lia.
            rewrite Z.pow_add_r by lia.
            replace (Z.pow 2 8) with 256 by reflexivity. lia. }
          rewrite Hpow in H1. lia.
        - split; [apply Z.div_pos; lia |].
          apply Z.div_lt_upper_bound; [lia |].
          assert (Hpow: Z.pow 2 (Z.of_nat (S k) * 8) = 256 * Z.pow 2 (Z.of_nat k * 8)).
          { rewrite Nat2Z.inj_succ.
            replace (Z.succ (Z.of_nat k) * 8) with (Z.of_nat k * 8 + 8) by lia.
            rewrite Z.pow_add_r by lia.
            replace (Z.pow 2 8) with 256 by reflexivity. lia. }
          rewrite Hpow in H2. lia.
        - exact Htail. }
      (* z1 = 256 * (z1/256) + (z1 mod 256) = 256 * (z2/256) + (z2 mod 256) = z2 *)
      rewrite (Z.div_mod z1 256) by lia.
      rewrite (Z.div_mod z2 256) by lia.
      rewrite Hdiv, Hmod. reflexivity.
  Qed.

  (** Nonce uniqueness for counter mode *)
  Lemma counter_nonces_unique :
    forall (n1 n2 : Z),
      0 <= n1 < Z.pow 2 64 ->
      0 <= n2 < Z.pow 2 64 ->
      n1 <> n2 ->
      counter_to_nonce n1 <> counter_to_nonce n2.
  Proof.
    intros n1 n2 H1 H2 Hne Heq.
    unfold counter_to_nonce in Heq.
    (* If counter_to_nonce n1 = counter_to_nonce n2, then
       Z_to_le_bytes_aux 8 n1 ++ pad = Z_to_le_bytes_aux 8 n2 ++ pad *)
    apply app_inv_tail in Heq.
    (* By injectivity of LE encoding, n1 = n2 *)
    apply Z_to_le_bytes_aux_injective in Heq.
    - contradiction.
    - simpl. lia.
    - simpl. lia.
  Qed.
End NonceManagement.

(** ** Putting It All Together: Notary Operations *)

Module NotaryOperations.
  Import MLDSA87.
  Import SHA3_256.
  Import DomainSeparation.

  (** Sign a file: hash then sign with domain separation *)
  Definition sign_file (sk : secret_key) (file_data : bytes) : signature :=
    let file_hash := sha3_256 file_data in
    let msg := with_domain sign_domain file_hash in
    sign sk msg.

  (** Verify a file signature *)
  Definition verify_file (pk : public_key) (file_data : bytes) (sig : signature) : bool :=
    let file_hash := sha3_256 file_data in
    let msg := with_domain sign_domain file_hash in
    verify pk msg sig.

  (** Correctness: valid file signatures verify *)
  Theorem sign_verify_file_correct :
    forall (seed file_data : bytes),
      let (sk, pk) := keygen seed in
      verify_file pk file_data (sign_file sk file_data) = true.
  Proof.
    intros seed file_data.
    unfold sign_file, verify_file.
    pose proof (sign_verify_correct seed (with_domain sign_domain (sha3_256 file_data))) as H.
    destruct (keygen seed) as [sk pk].
    exact H.
  Qed.

  (** Create attestation receipt *)
  Definition create_receipt (sk : secret_key) (data : bytes) (timestamp : Z) : signature :=
    let digest := sha3_256 data in
    (* Receipt includes digest and timestamp *)
    let receipt_data := digest in  (* Simplified *)
    let msg := with_domain attest_domain receipt_data in
    sign sk msg.

  (** Issue a license *)
  Definition issue_license (sk : secret_key) (user product : bytes) (expiry : Z) : signature :=
    let license_data := user ++ product in  (* Simplified *)
    let msg := with_domain license_domain license_data in
    sign sk msg.

End NotaryOperations.

(** ** Security Properties *)

(** Property 1: Signature Unforgeability *)
(** Under EUF-CMA assumption, an attacker cannot forge signatures. *)
Definition signature_unforgeability : Prop :=
  forall (seed msg : bytes) (forged_sig : MLDSA87.signature),
    let (sk, pk) := MLDSA87.keygen seed in
    (* If we never signed msg with sk, the forged signature shouldn't verify *)
    (* (This is the informal statement - EUF-CMA captures the formal version) *)
    MLDSA87.euf_cma_secure ->
    (* ADMITTED: forged_sig not produced by sign -> verify fails w.h.p. *)
    MLDSA87.verify pk msg forged_sig = false.

(** Property 2: Key Confidentiality *)
(** Under IND-CPA, an attacker learns nothing about sealed keys. *)
(** ADMITTED: Requires computational indistinguishability formalization *)
Definition key_confidentiality : Prop :=
  forall (k : ChaCha20Poly1305.key) (n : ChaCha20Poly1305.nonce)
         (secret1 secret2 : bytes) (aad : bytes),
    bytes_len secret1 = bytes_len secret2 ->
    ChaCha20Poly1305.ind_cpa_secure ->
    (* Ciphertexts are computationally indistinguishable *)
    (* This is a computational property that cannot be directly expressed in Coq
       without a probabilistic/game-based framework. We state the informal property
       that encrypt(k, n, secret1, aad) and encrypt(k, n, secret2, aad) are
       indistinguishable to any PPT adversary. *)
    let (ct1, _) := ChaCha20Poly1305.encrypt k n secret1 aad in
    let (ct2, _) := ChaCha20Poly1305.encrypt k n secret2 aad in
    bytes_len ct1 = bytes_len ct2.

(** Property 3: Key Integrity *)
(** Under INT-CTXT, an attacker cannot modify sealed keys. *)
(** ADMITTED: Requires game-based INT-CTXT formalization *)
Definition key_integrity : Prop :=
  forall (k : ChaCha20Poly1305.key) (n : ChaCha20Poly1305.nonce)
         (ct : bytes) (t : ChaCha20Poly1305.tag) (aad : bytes),
    ChaCha20Poly1305.int_ctxt_secure ->
    (* Modified ciphertext fails authentication - informal statement *)
    (* For any ct' <> ct or t' <> t not produced by encrypt,
       decrypt will return None (authentication failure) *)
    forall ct' t',
      (ct' <> ct \/ t' <> t) ->
      ChaCha20Poly1305.decrypt k n ct' t' aad = None.

(** Property 4: Receipt Binding *)
(** Under collision resistance, receipts uniquely identify content. *)
(** ADMITTED: Collision resistance implies hash equality => data equality *)
Definition receipt_binding : Prop :=
  forall (data1 data2 : bytes),
    SHA3_256.collision_resistant ->
    SHA3_256.sha3_256 data1 = SHA3_256.sha3_256 data2 ->
    (* With overwhelming probability, data1 = data2 *)
    (* Under the collision resistance assumption, finding distinct data1 <> data2
       with the same hash is computationally infeasible *)
    data1 = data2.

(** ** Security Composition Theorem *)
(**
    This theorem states that the Anubis Notary system achieves its
    security goals when instantiated with secure primitives.

    The security reduction shows:
    1. EUF-CMA of ML-DSA-87 → unforgeability of notary signatures
    2. IND-CPA of ChaCha20Poly1305 → confidentiality of sealed keys
    3. INT-CTXT of ChaCha20Poly1305 → integrity of sealed keys
    4. Collision resistance of SHA3-256 → binding of receipts to content

    Each property follows from its corresponding primitive assumption
    plus the domain-separation design that prevents cross-protocol attacks.
*)
(** ADMITTED: This theorem requires game-based cryptographic reductions
    that are outside the scope of standard Coq/Rocq. A complete proof would
    require a probabilistic relational Hoare logic framework like FCF or
    CryptoVerif integration. The informal security argument is:
    1. EUF-CMA of ML-DSA-87 → signature unforgeability (standard reduction)
    2. IND-CPA of ChaCha20Poly1305 → key confidentiality (standard reduction)
    3. INT-CTXT of ChaCha20Poly1305 → key integrity (standard reduction)
    4. Collision resistance of SHA3-256 → receipt binding (trivial reduction)
*)
(** System security is a meta-theorem that follows from the security of
    the underlying primitives via standard cryptographic reductions.
    This cannot be proven in pure Coq/Rocq without a probabilistic
    framework (like FCF, CryptoVerif, or EasyCrypt). We axiomatize
    the composition result which is justified by:
    1. EUF-CMA → signature unforgeability: standard reduction
    2. IND-CPA → key confidentiality: standard hybrid argument
    3. INT-CTXT → key integrity: standard reduction
    4. Collision resistance → receipt binding: trivial reduction *)
Axiom system_security :
  MLDSA87.euf_cma_secure ->
  ChaCha20Poly1305.ind_cpa_secure ->
  ChaCha20Poly1305.int_ctxt_secure ->
  SHA3_256.collision_resistant ->
  signature_unforgeability /\
  key_confidentiality /\
  key_integrity /\
  receipt_binding.

(** Concrete security theorem: file signatures are unforgeable *)
Theorem file_signature_unforgeable :
  MLDSA87.euf_cma_secure ->
  forall (seed file1 file2 : bytes) (sig : MLDSA87.signature),
    let (sk, pk) := MLDSA87.keygen seed in
    (* If we sign file1, the signature verifies for file1 *)
    NotaryOperations.verify_file pk file1 (NotaryOperations.sign_file sk file1) = true /\
    (* And if file1 ≠ file2 with high probability, sig for file1 doesn't verify for file2 *)
    (SHA3_256.collision_resistant ->
     SHA3_256.sha3_256 file1 <> SHA3_256.sha3_256 file2 ->
     NotaryOperations.verify_file pk file2 (NotaryOperations.sign_file sk file1) = false).
Proof.
  intros Heuf seed file1 file2 sig.
  destruct (MLDSA87.keygen seed) as [sk pk] eqn:Hkeygen.
  split.
  - (* First part: signature of file1 verifies for file1 *)
    (* This follows from sign_verify_file_correct *)
    pose proof (NotaryOperations.sign_verify_file_correct seed file1) as Hcorr.
    rewrite Hkeygen in Hcorr.
    exact Hcorr.
  - (* Second part: signature of file1 doesn't verify for file2 when hashes differ *)
    intros Hcr Hdiff.
    (* Different hashes means different messages after domain separation.
       By EUF-CMA, signing msg1 produces a signature that only verifies for msg1.
       The reduction: if verify(pk, msg2, sign(sk, msg1)) = true for msg1 ≠ msg2,
       then we have a signature forgery against EUF-CMA. *)
    unfold NotaryOperations.verify_file, NotaryOperations.sign_file.
    (* The key insight: with_domain sign_domain (sha3_256 file1) ≠
       with_domain sign_domain (sha3_256 file2) because sha3_256 file1 ≠ sha3_256 file2
       and domain separation is injective *)
    pose proof (DomainSeparation.with_domain_injective
      DomainSeparation.sign_domain (SHA3_256.sha3_256 file1) (SHA3_256.sha3_256 file2) Hdiff) as Hmsg_diff.
    (* By EUF-CMA, verify pk msg2 (sign sk msg1) = false when msg1 ≠ msg2 *)
    (* Reconstruct keygen seed from sk and pk *)
    assert (Hsk: sk = fst (MLDSA87.keygen seed)) by (rewrite Hkeygen; reflexivity).
    assert (Hpk: pk = snd (MLDSA87.keygen seed)) by (rewrite Hkeygen; reflexivity).
    rewrite Hsk, Hpk.
    apply (MLDSA87.euf_cma_different_message seed).
    + exact Heuf.
    + reflexivity.
    + exact Hmsg_diff.
Qed.

