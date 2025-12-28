(** Proof for signatures_needed: Threshold signature calculation *)
From Stdlib Require Import ZArith Lia.
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function signatures_needed computes max(0, threshold - current).

    Implementation:
      pub fn signatures_needed(current: u32, threshold: u32) -> u32 {
          threshold.saturating_sub(current)
      }

    Specification:
      #[rr::params("current" : "Z", "threshold" : "Z")]
      #[rr::args("current", "threshold")]
      #[rr::requires("0 ≤ current")]
      #[rr::requires("0 < threshold")]
      #[rr::returns("Z.max 0 (threshold - current)")]
*)

Open Scope Z_scope.

(** Model for signatures needed calculation *)
Definition signatures_needed_model (current threshold : Z) : Z :=
  Z.max 0 (threshold - current).

(** Result is always non-negative *)
Lemma signatures_needed_nonneg : forall current threshold,
  0 <= signatures_needed_model current threshold.
Proof.
  intros. unfold signatures_needed_model.
  apply Z.le_max_l.
Qed.

(** When threshold is met, result is 0 *)
Theorem signatures_needed_zero_when_met : forall current threshold,
  0 <= current -> 0 < threshold ->
  threshold <= current ->
  signatures_needed_model current threshold = 0.
Proof.
  intros current threshold Hc Ht Hmet.
  unfold signatures_needed_model.
  rewrite Z.max_l; lia.
Qed.

(** When threshold not met, result is positive *)
Theorem signatures_needed_positive_when_not_met : forall current threshold,
  0 <= current -> 0 < threshold ->
  current < threshold ->
  0 < signatures_needed_model current threshold.
Proof.
  intros current threshold Hc Ht Hnot_met.
  unfold signatures_needed_model.
  rewrite Z.max_r; lia.
Qed.

(** Adding one signature decreases needed count (when not met) *)
Theorem signatures_needed_decreases : forall current threshold,
  0 <= current -> 0 < threshold ->
  current < threshold ->
  signatures_needed_model (current + 1) threshold <
  signatures_needed_model current threshold.
Proof.
  intros current threshold Hc Ht Hlt.
  unfold signatures_needed_model.
  rewrite Z.max_r by lia.
  destruct (Z.max_dec 0 (threshold - (current + 1))) as [Hcase | Hcase];
    rewrite Hcase; lia.
Qed.

(** Eventually reaches zero *)
Theorem signatures_needed_eventually_zero : forall current threshold,
  0 <= current -> 0 < threshold ->
  exists n, 0 <= n /\ signatures_needed_model (current + n) threshold = 0.
Proof.
  intros current threshold Hc Ht.
  destruct (Z_lt_le_dec current threshold) as [Hlt | Hge].
  - (* current < threshold *)
    exists (threshold - current).
    split.
    + lia.
    + unfold signatures_needed_model.
      rewrite Z.max_l; lia.
  - (* current >= threshold, already met *)
    exists 0.
    split.
    + lia.
    + rewrite Z.add_0_r.
      apply signatures_needed_zero_when_met; lia.
Qed.

(** Exact count: needed = threshold - current when not met *)
Theorem signatures_needed_exact : forall current threshold,
  0 <= current -> 0 < threshold ->
  current < threshold ->
  signatures_needed_model current threshold = threshold - current.
Proof.
  intros current threshold Hc Ht Hlt.
  unfold signatures_needed_model.
  rewrite Z.max_r; lia.
Qed.

(** Monotonicity: more signatures means less needed *)
Theorem signatures_needed_monotonic : forall c1 c2 threshold,
  0 <= c1 -> c1 <= c2 -> 0 < threshold ->
  signatures_needed_model c2 threshold <= signatures_needed_model c1 threshold.
Proof.
  intros c1 c2 threshold Hc1 Hle Ht.
  unfold signatures_needed_model.
  apply Z.max_le_compat_l.
  lia.
Qed.

Close Scope Z_scope.

End proof.
