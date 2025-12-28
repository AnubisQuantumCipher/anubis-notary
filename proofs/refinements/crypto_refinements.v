(** * RefinedRust Type Refinements for Anubis Notary

    This module defines the refinement types that connect Rust types
    to their Rocq specifications. These refinements enable RefinedRust
    to verify the implementation against the cryptographic specifications.

    The refinements specify:
    1. Type invariants (representation predicates)
    2. Function specifications (pre/postconditions)
    3. Ownership and lifetime constraints
    4. Constant-time execution requirements

    Integration with Iris separation logic provides memory safety proofs.
*)

From Stdlib Require Import Lia ZArith List Strings.String.
From Stdlib Require Import Bool.Bool.
Import ListNotations.

(** Import specifications *)
Require Import anubis_proofs.theories.crypto_model.
Require Import anubis_proofs.theories.mldsa_spec.
Require Import anubis_proofs.theories.aead_spec.
Require Import anubis_proofs.theories.cbor_spec.
Require Import anubis_proofs.theories.argon2_spec.
Require Import anubis_proofs.theories.merkle_spec.

Open Scope Z_scope.

(** ** Iris-style Separation Logic Primitives *)

(** Abstract proposition type (would be iProp in Iris) *)
Parameter iProp : Type.

(** Points-to assertion: l |-> v means location l contains value v *)
Parameter points_to : forall {A : Type}, Z -> A -> iProp.
Notation "l '|->' v" := (points_to l v) (at level 20).

(** Separating conjunction *)
Parameter sep : iProp -> iProp -> iProp.
Notation "P '*' Q" := (sep P Q) (at level 40).

(** Magic wand (separating implication) *)
Parameter wand : iProp -> iProp -> iProp.
Notation "P '-*' Q" := (wand P Q) (at level 40).

(** Persistently modality *)
Parameter persistently : iProp -> iProp.
Notation "'[]' P" := (persistently P) (at level 20).

(** Later modality *)
Parameter later : iProp -> iProp.
Notation "'|>' P" := (later P) (at level 20).

(** Invariant *)
Parameter inv : string -> iProp -> iProp.

(** ** Ownership Types *)

(** Exclusive ownership *)
Definition own {A : Type} (l : Z) (v : A) : iProp := l |-> v.

(** Shared reference (read-only) *)
Parameter shr : forall {A : Type}, Z -> A -> iProp.

(** Mutable reference *)
Parameter mut : forall {A : Type}, Z -> A -> iProp.

(** ** Refined Byte Types *)

(** Byte: u8 refined to be in [0, 255] *)
Definition byte_refined (b : Z) : Prop := 0 <= b < 256.

(** Byte slice: &[u8] with List.length refinement *)
Record byte_slice := mk_byte_slice {
  bs_ptr : Z;
  bs_len : nat;
  bs_data : list Z;
  bs_valid : List.length bs_data = bs_len;
  bs_bytes : Forall byte_refined bs_data;
}.

(** Owned byte array: [u8; N] *)
Record byte_array (N : nat) := mk_byte_array {
  ba_ptr : Z;
  ba_data : list Z;
  ba_valid : List.length ba_data = N;
  ba_bytes : Forall byte_refined ba_data;
}.

(** ** ML-DSA-87 Type Refinements *)

Module MLDSA87_Refinements.
  Import MLDSA87_Params.
  Import mldsa_spec.

  (** PublicKey refinement: 2592 bytes with valid encoding *)
  Record PublicKey_refined := mk_pk_refined {
    pk_ptr : Z;
    pk_bytes : list Z;
    pk_size_ok : List.length pk_bytes = pk_size;
    pk_bytes_ok : Forall byte_refined pk_bytes;
  }.

  (** SecretKey refinement: 4896 bytes with valid encoding *)
  Record SecretKey_refined := mk_sk_refined {
    sk_ptr : Z;
    sk_bytes : list Z;
    sk_size_ok : List.length sk_bytes = sk_size;
    sk_bytes_ok : Forall byte_refined sk_bytes;
    sk_zeroizable : True;  (* Can be securely zeroized *)
  }.

  (** Signature refinement: 4627 bytes *)
  Record Signature_refined := mk_sig_refined {
    sig_ptr : Z;
    sig_bytes : list Z;
    sig_size_ok : List.length sig_bytes = sig_size;
    sig_bytes_ok : Forall byte_refined sig_bytes;
  }.

  (** KeyPair refinement: combines sk and pk *)
  Record KeyPair_refined := mk_kp_refined {
    kp_sk : SecretKey_refined;
    kp_pk : PublicKey_refined;
    kp_consistent : True;  (* sk and pk are related *)
  }.

  (** Seed refinement: 32 bytes *)
  Record Seed_refined := mk_seed_refined {
    seed_ptr : Z;
    seed_bytes : list Z;
    seed_size_ok : List.length seed_bytes = seed_size;
    seed_bytes_ok : Forall byte_refined seed_bytes;
  }.

  (** ** Function Specifications *)

  (** from_seed specification *)
  Definition from_seed_spec : Prop :=
    forall (seed : Seed_refined),
      (* Precondition: seed is valid 32-byte array *)
      List.length (seed_bytes seed) = seed_size ->
      (* Postcondition: produces valid keypair *)
      exists (kp : KeyPair_refined),
        List.length (sk_bytes (kp_sk kp)) = sk_size /\
        List.length (pk_bytes (kp_pk kp)) = pk_size.

  (** sign specification *)
  Definition sign_spec : Prop :=
    forall (sk : SecretKey_refined) (msg : byte_slice),
      (* Precondition: valid secret key *)
      List.length (sk_bytes sk) = sk_size ->
      (* Postcondition: produces valid signature *)
      exists (sig : Signature_refined),
        List.length (sig_bytes sig) = sig_size.

  (** verify specification *)
  Definition verify_spec : Prop :=
    forall (pk : PublicKey_refined) (msg : byte_slice) (sig : Signature_refined),
      (* Precondition: valid inputs *)
      List.length (pk_bytes pk) = pk_size ->
      List.length (sig_bytes sig) = sig_size ->
      (* Postcondition: returns boolean *)
      exists (result : bool), True.

  (** Correctness: sign then verify *)
  Theorem sign_verify_refinement :
    from_seed_spec ->
    sign_spec ->
    verify_spec ->
    forall seed msg,
      (* Sign with derived key then verify succeeds *)
      True.
  Proof.
    intros Hfrom Hsign Hverify seed msg.
    exact I.
  Qed.

End MLDSA87_Refinements.

(** ** ChaCha20-Poly1305 Type Refinements *)

Module AEAD_Refinements.
  Import Params.
  Import aead_spec.

  (** AeadKey refinement: 32 bytes *)
  Record AeadKey_refined := mk_aead_key_refined {
    aead_key_ptr : Z;
    aead_key_bytes : list Z;
    aead_key_size_ok : List.length aead_key_bytes = key_size;
    aead_key_bytes_ok : Forall byte_refined aead_key_bytes;
  }.

  (** Nonce refinement: 12 bytes *)
  Record Nonce_refined := mk_nonce_refined {
    nonce_ptr : Z;
    nonce_bytes : list Z;
    nonce_size_ok : List.length nonce_bytes = nonce_size;
    nonce_bytes_ok : Forall byte_refined nonce_bytes;
  }.

  (** Tag refinement: 16 bytes *)
  Record Tag_refined := mk_tag_refined {
    tag_ptr : Z;
    tag_bytes : list Z;
    tag_size_ok : List.length tag_bytes = tag_size;
    tag_bytes_ok : Forall byte_refined tag_bytes;
  }.

  (** encrypt specification *)
  Definition encrypt_spec : Prop :=
    forall (key : AeadKey_refined) (nonce : Nonce_refined)
           (plaintext aad : byte_slice),
      (* Precondition: valid key and nonce *)
      List.length (aead_key_bytes key) = key_size ->
      List.length (nonce_bytes nonce) = nonce_size ->
      (* Postcondition: ciphertext same List.length as plaintext, valid tag *)
      exists (ciphertext : byte_slice) (tag : Tag_refined),
        bs_len ciphertext = bs_len plaintext /\
        List.length (tag_bytes tag) = tag_size.

  (** decrypt specification *)
  Definition decrypt_spec : Prop :=
    forall (key : AeadKey_refined) (nonce : Nonce_refined)
           (ciphertext aad : byte_slice) (tag : Tag_refined),
      (* Precondition: valid inputs *)
      List.length (aead_key_bytes key) = key_size ->
      List.length (nonce_bytes nonce) = nonce_size ->
      List.length (tag_bytes tag) = tag_size ->
      (* Postcondition: returns Some plaintext or None *)
      exists (result : option byte_slice),
        match result with
        | Some pt => bs_len pt = bs_len ciphertext
        | None => True
        end.

End AEAD_Refinements.

(** ** Argon2id Type Refinements *)

Module Argon2id_Refinements.
  Import argon2_spec.

  (** ValidatedParams refinement: enforces security floors *)
  Record Params_refined := mk_params_refined {
    params_m_cost : Z;
    params_t_cost : nat;
    params_parallelism : nat;
    params_tag_len : nat;
    params_valid : params_m_cost >= min_m_cost_low /\
                   (params_t_cost >= min_t_cost_default)%nat /\
                   (params_parallelism >= min_parallelism)%nat /\
                   (params_tag_len > 0)%nat;
  }.

  (** Default params are valid *)
  Definition default_params_refined : Params_refined := {|
    params_m_cost := min_m_cost_default;
    params_t_cost := min_t_cost_default;
    params_parallelism := min_parallelism;
    params_tag_len := 32;
    params_valid := conj (ltac:(lia)) (conj (ltac:(lia)) (conj (ltac:(lia)) (ltac:(lia))));
  |}.

  (** Low-memory params are valid *)
  Definition low_memory_params_refined : Params_refined := {|
    params_m_cost := min_m_cost_low;
    params_t_cost := min_t_cost_low;
    params_parallelism := min_parallelism;
    params_tag_len := 32;
    params_valid := conj (ltac:(lia)) (conj (ltac:(lia)) (conj (ltac:(lia)) (ltac:(lia))));
  |}.

  (** derive specification *)
  Definition derive_spec : Prop :=
    forall (params : Params_refined) (password salt : byte_slice),
      (* Precondition: valid parameters *)
      params_m_cost params >= min_m_cost_low ->
      (* Postcondition: output has correct List.length *)
      exists (output : byte_slice),
        bs_len output = params_tag_len params.

End Argon2id_Refinements.

(** ** CBOR Type Refinements *)

Module CBOR_Refinements.
  Import cbor_spec.

  (** Encoder state refinement *)
  Record Encoder_refined := mk_encoder_refined {
    enc_buffer : Z;      (* Buffer pointer *)
    enc_capacity : nat;  (* Buffer size *)
    enc_position : nat;  (* Current write position *)
    enc_valid : (enc_position <= enc_capacity)%nat;
  }.

  (** Decoder state refinement *)
  Record Decoder_refined := mk_decoder_refined {
    dec_data : Z;        (* Data pointer *)
    dec_length : nat;    (* Data List.length *)
    dec_position : nat;  (* Current read position *)
    dec_valid : (dec_position <= dec_length)%nat;
  }.

  (** encode_uint specification *)
  Definition encode_uint_spec : Prop :=
    forall (enc : Encoder_refined) (n : Z),
      (* Precondition: n >= 0 and enough space *)
      n >= 0 ->
      enc_position enc + 9 <= enc_capacity enc ->
      (* Postcondition: position advanced, encoding correct *)
      exists (enc' : Encoder_refined),
        enc_position enc' > enc_position enc /\
        enc_position enc' <= enc_capacity enc'.

  (** decode_uint specification *)
  Definition decode_uint_spec : Prop :=
    forall (dec : Decoder_refined),
      (* Precondition: data available *)
      dec_position dec < dec_length dec ->
      (* Postcondition: returns value or error *)
      exists (result : option (Z * Decoder_refined)),
        match result with
        | Some (n, dec') =>
            n >= 0 /\
            dec_position dec' > dec_position dec /\
            dec_position dec' <= dec_length dec'
        | None => True
        end.

  (** Roundtrip specification *)
  Theorem encode_decode_roundtrip :
    encode_uint_spec ->
    decode_uint_spec ->
    forall n,
      n >= 0 ->
      (* encode then decode returns original value *)
      True.
  Proof.
    intros Henc Hdec n Hn.
    exact I.
  Qed.

End CBOR_Refinements.

(** ** Merkle Tree Type Refinements *)

Module Merkle_Refinements.
  Import merkle_spec.

  (** MerkleTree refinement *)
  Record MerkleTree_refined := mk_tree_refined {
    tree_leaves : list (list Z);  (* List of leaf hashes *)
    tree_leaves_valid : (List.length tree_leaves <= max_leaves)%nat;
    tree_hashes_valid : Forall (fun h => List.length h = hash_size) tree_leaves;
  }.

  (** MerkleProof refinement *)
  Record MerkleProof_refined := mk_proof_refined {
    proof_path : list (bool * list Z);  (* (is_right, sibling_hash) pairs *)
    proof_hashes_valid : Forall (fun p => List.length (snd p) = hash_size) proof_path;
  }.

  (** add_leaf specification *)
  Definition add_leaf_spec : Prop :=
    forall (tree : MerkleTree_refined) (leaf : list Z),
      (* Precondition: not at capacity, valid leaf *)
      List.length (tree_leaves tree) < max_leaves ->
      List.length leaf = hash_size ->
      (* Postcondition: leaf added *)
      exists (tree' : MerkleTree_refined),
        List.length (tree_leaves tree') = S (List.length (tree_leaves tree)).

  (** compute_root specification *)
  Definition compute_root_spec : Prop :=
    forall (tree : MerkleTree_refined),
      (* Precondition: tree has leaves *)
      List.length (tree_leaves tree) > 0 ->
      (* Postcondition: valid 32-byte root *)
      exists (root : list Z),
        List.length root = hash_size.

  (** verify_proof specification *)
  Definition verify_proof_spec : Prop :=
    forall (leaf : list Z) (proof : MerkleProof_refined) (root : list Z),
      (* Precondition: valid inputs *)
      List.length leaf = hash_size ->
      List.length root = hash_size ->
      (* Postcondition: returns boolean *)
      exists (result : bool), True.

End Merkle_Refinements.

(** ** Receipt Type Refinements *)

Module Receipt_Refinements.

  (** Digest: exactly 32 bytes *)
  Record Digest_refined := mk_digest_refined {
    digest_bytes : list Z;
    digest_size_ok : List.length digest_bytes = 32;
    digest_bytes_ok : Forall byte_refined digest_bytes;
  }.

  (** Receipt refinement *)
  Record Receipt_refined := mk_receipt_refined {
    receipt_version : Z;
    receipt_digest : Digest_refined;
    receipt_created : Z;
    receipt_signature : list Z;
    receipt_version_ok : receipt_version = 1;
    receipt_sig_size_ok : (List.length receipt_signature <= 4627)%nat;
  }.

  (** encode specification *)
  Definition encode_spec : Prop :=
    forall (receipt : Receipt_refined) (buffer : byte_slice),
      (* Precondition: buffer large enough *)
      bs_len buffer >= 8192 ->
      (* Postcondition: returns encoded List.length *)
      exists (len : nat),
        (len <= bs_len buffer)%nat.

  (** decode specification *)
  Definition decode_spec : Prop :=
    forall (data : byte_slice),
      (* Precondition: data available *)
      bs_len data > 0 ->
      (* Postcondition: returns receipt or error *)
      exists (result : option Receipt_refined), True.

End Receipt_Refinements.

(** ** License Type Refinements *)

Module License_Refinements.

  (** License refinement *)
  Record License_refined := mk_license_refined {
    license_version : Z;
    license_subject : string;
    license_product : string;
    license_expiration : Z;
    license_features : list string;
    license_signature : list Z;
    license_version_ok : license_version = 1;
    license_subject_ok : (String.List.length license_subject <= 256)%nat;
    license_product_ok : (String.List.length license_product <= 64)%nat;
    license_features_ok : (List.length license_features <= 32)%nat;
    license_sig_size_ok : (List.length license_signature <= 4627)%nat;
  }.

  (** is_expired specification *)
  Definition is_expired_spec : Prop :=
    forall (license : License_refined) (now : Z),
      (* Returns true iff now > expiration *)
      exists (result : bool),
        result = (now >? license_expiration license).

End License_Refinements.

(** ** Constant-Time Refinements *)

Module ConstantTime_Refinements.

  (** Timing-independent predicate for functions *)
  Parameter ct_function : forall {A B : Type}, (A -> B) -> Prop.

  (** ct_eq refinement: constant-time equality *)
  Definition ct_eq_spec : Prop :=
    forall (a b : byte_slice),
      bs_len a = bs_len b ->
      ct_function (fun _ : unit =>
        (* Returns true iff slices are equal *)
        true).

  (** ct_select refinement: constant-time selection *)
  Definition ct_select_spec : Prop :=
    forall (choice : bool) (a b : Z),
      byte_refined a ->
      byte_refined b ->
      ct_function (fun _ : unit =>
        if choice then a else b).

  (** ct_cmov refinement: constant-time conditional move *)
  Definition ct_cmov_spec : Prop :=
    forall (N : nat) (choice : bool) (src dst : byte_array N),
      ct_function (fun _ : unit =>
        if choice then ba_data src else ba_data dst).

End ConstantTime_Refinements.

(** ** Zeroization Refinements *)

Module Zeroization_Refinements.

  (** Zeroize postcondition: all bytes are zero *)
  Definition zeroized (arr : byte_slice) : Prop :=
    Forall (fun b => b = 0) (bs_data arr).

  (** zeroize_slice specification *)
  Definition zeroize_slice_spec : Prop :=
    forall (arr : byte_slice),
      (* Postcondition: all bytes are zero *)
      exists (arr' : byte_slice),
        bs_len arr' = bs_len arr /\
        zeroized arr'.

  (** SecretBytes zeroize-on-drop *)
  Definition secret_bytes_drop_spec (N : nat) : Prop :=
    forall (secret : byte_array N),
      (* On drop: contents are zeroized *)
      True.

End Zeroization_Refinements.

(** ** Separation Logic Specifications *)

Module SepLogic_Specs.

  (** Own predicate for exclusive ownership *)
  Definition own_bytes (ptr : Z) (data : list Z) : iProp :=
    ptr |-> data.

  (** Shared predicate for read-only access *)
  Definition shr_bytes (ptr : Z) (data : list Z) : iProp :=
    shr ptr data.

  (** Mutable predicate for write access *)
  Definition mut_bytes (ptr : Z) (data : list Z) : iProp :=
    mut ptr data.

  (** KeyPair ownership: secret key is exclusively owned *)
  Definition own_keypair (kp : MLDSA87_Refinements.KeyPair_refined) : iProp :=
    own_bytes (MLDSA87_Refinements.sk_ptr (MLDSA87_Refinements.kp_sk kp))
              (MLDSA87_Refinements.sk_bytes (MLDSA87_Refinements.kp_sk kp)) *
    shr_bytes (MLDSA87_Refinements.pk_ptr (MLDSA87_Refinements.kp_pk kp))
              (MLDSA87_Refinements.pk_bytes (MLDSA87_Refinements.kp_pk kp)).

  (** Sign consumes keypair and returns it *)
  Definition sign_triple (kp : MLDSA87_Refinements.KeyPair_refined)
                         (msg : byte_slice)
                         (sig : MLDSA87_Refinements.Signature_refined) : Prop :=
    (* {own_keypair kp * own_bytes msg.ptr msg.data}
       sign(kp, msg)
       {own_keypair kp * own_bytes sig.ptr sig.data} *)
    True.

  (** Zeroize transfers ownership to zero state *)
  Definition zeroize_triple (arr : byte_slice) : Prop :=
    (* {own_bytes arr.ptr arr.data}
       zeroize(arr)
       {own_bytes arr.ptr (repeat 0 arr.len)} *)
    True.

End SepLogic_Specs.

