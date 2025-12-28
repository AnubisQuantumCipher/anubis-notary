(** Proof for nonce_index: Deterministic nonce derivation *)
From Stdlib Require Import ZArith Lia.
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function nonce_index computes (key_id << 32) | counter.

    Implementation:
      pub fn nonce_index(key_id: u32, counter: u32) -> u64 {
          ((key_id as u64) << 32) | (counter as u64)
      }

    Specification:
      #[rr::params("key_id" : "Z", "counter" : "Z")]
      #[rr::args("key_id", "counter")]
      #[rr::requires("0 ≤ key_id < 2^32")]
      #[rr::requires("0 ≤ counter < 2^32")]
      #[rr::returns("Z.lor (Z.shiftl key_id 32) counter")]
*)

Open Scope Z_scope.

(** Model for nonce index construction *)
Definition nonce_index_model (key_id counter : Z) : Z :=
  Z.lor (Z.shiftl key_id 32) counter.

(** The result is within u64 range *)
Lemma nonce_index_range : forall key_id counter,
  0 <= key_id < 2^32 ->
  0 <= counter < 2^32 ->
  0 <= nonce_index_model key_id counter < 2^64.
Proof.
  intros key_id counter [Hk1 Hk2] [Hc1 Hc2].
  unfold nonce_index_model.
  split.
  - apply Z.lor_nonneg; split.
    + apply Z.shiftl_nonneg. lia.
    + lia.
  - (* Upper bound: (key_id << 32) | counter < 2^64 *)
    (* key_id << 32 < 2^64 and counter < 2^32 < 2^64 *)
    (* Their OR is bounded by their sum *)
    assert (Z.shiftl key_id 32 < 2^64) as Hshift.
    { rewrite Z.shiftl_mul_pow2 by lia.
      assert (key_id * 2^32 < 2^32 * 2^32) by lia.
      rewrite <- Z.pow_add_r in H by lia.
      lia. }
    assert (Z.shiftl key_id 32 + counter < 2^64) as Hsum.
    { rewrite Z.shiftl_mul_pow2 by lia.
      assert (2^32 * 2^32 = 2^64) as H2.
      { rewrite <- Z.pow_add_r by lia. reflexivity. }
      lia. }
    (* lor <= add for non-negative *)
    apply Z.lor_le. lia. lia.
Qed.

(** Key property: nonce_index is injective *)
Theorem nonce_index_injective : forall k1 c1 k2 c2,
  0 <= k1 < 2^32 -> 0 <= c1 < 2^32 ->
  0 <= k2 < 2^32 -> 0 <= c2 < 2^32 ->
  nonce_index_model k1 c1 = nonce_index_model k2 c2 ->
  k1 = k2 /\ c1 = c2.
Proof.
  intros k1 c1 k2 c2 Hk1 Hc1 Hk2 Hc2 Heq.
  unfold nonce_index_model in Heq.
  (* The lower 32 bits give counter, upper 32 bits give key_id *)
  (* This follows from the disjointness of the shifted key_id and counter *)
  split.
  - (* Extract key_id by shifting right 32 *)
    assert (Z.shiftr (nonce_index_model k1 c1) 32 = k1) as H1.
    { unfold nonce_index_model.
      rewrite Z.shiftr_lor.
      rewrite Z.shiftr_shiftl_l by lia.
      rewrite Z.sub_diag, Z.shiftl_0_r.
      rewrite Z.shiftr_small by lia.
      rewrite Z.lor_0_r. reflexivity. }
    assert (Z.shiftr (nonce_index_model k2 c2) 32 = k2) as H2.
    { unfold nonce_index_model.
      rewrite Z.shiftr_lor.
      rewrite Z.shiftr_shiftl_l by lia.
      rewrite Z.sub_diag, Z.shiftl_0_r.
      rewrite Z.shiftr_small by lia.
      rewrite Z.lor_0_r. reflexivity. }
    rewrite Heq in H1. rewrite H1, H2. reflexivity.
  - (* Extract counter by masking lower 32 bits *)
    assert (Z.land (nonce_index_model k1 c1) (2^32 - 1) = c1) as H1.
    { unfold nonce_index_model.
      rewrite Z.land_lor_distr_l.
      rewrite Z.shiftl_land.
      assert (Z.land (Z.shiftl k1 32) (2^32 - 1) = 0) as Hzero.
      { apply Z.bits_inj. intros n.
        rewrite Z.land_spec, Z.shiftl_spec by lia.
        destruct (Z.ltb n 32) eqn:Hn.
        - apply Z.ltb_lt in Hn.
          rewrite Z.testbit_neg_r by lia.
          apply andb_false_l.
        - apply Z.ltb_ge in Hn.
          assert (Z.testbit (2^32 - 1) n = false) as Hmask.
          { apply Z.bits_above_log2. lia. simpl. lia. }
          rewrite Hmask. apply andb_false_r. }
      rewrite Hzero, Z.lor_0_l.
      rewrite Z.land_ones by lia.
      apply Z.mod_small. lia. }
    assert (Z.land (nonce_index_model k2 c2) (2^32 - 1) = c2) as H2.
    { unfold nonce_index_model.
      rewrite Z.land_lor_distr_l.
      rewrite Z.shiftl_land.
      assert (Z.land (Z.shiftl k2 32) (2^32 - 1) = 0) as Hzero.
      { apply Z.bits_inj. intros n.
        rewrite Z.land_spec, Z.shiftl_spec by lia.
        destruct (Z.ltb n 32) eqn:Hn.
        - apply Z.ltb_lt in Hn.
          rewrite Z.testbit_neg_r by lia.
          apply andb_false_l.
        - apply Z.ltb_ge in Hn.
          assert (Z.testbit (2^32 - 1) n = false) as Hmask.
          { apply Z.bits_above_log2. lia. simpl. lia. }
          rewrite Hmask. apply andb_false_r. }
      rewrite Hzero, Z.lor_0_l.
      rewrite Z.land_ones by lia.
      apply Z.mod_small. lia. }
    rewrite Heq in H1. rewrite H1, H2. reflexivity.
Qed.

Close Scope Z_scope.

End proof.
