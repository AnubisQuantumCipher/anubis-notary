(** Proof for valid_threshold: Check threshold validity *)
From Stdlib Require Import ZArith Lia.
From caesium Require Import lang notation.
From refinedrust Require Import typing shims.
From refinedrust.examples.anubis_verified.generated Require Import
  generated_code_anubis_verified
  generated_specs_anubis_verified.

Set Default Proof Using "Type".

Section proof.
Context `{RRGS : !refinedrustGS Σ}.

(** The function valid_threshold checks if threshold <= n_signers.

    Implementation:
      pub fn valid_threshold(threshold: u32, n_signers: u32) -> bool {
          threshold <= n_signers
      }

    Specification:
      #[rr::params("threshold" : "Z", "n_signers" : "Z")]
      #[rr::args("threshold", "n_signers")]
      #[rr::requires("0 < threshold")]
      #[rr::requires("0 < n_signers")]
      #[rr::returns("bool_decide (threshold ≤ n_signers)")]
*)

Open Scope Z_scope.

(** Threshold validity model *)
Definition valid_threshold_model (threshold n_signers : Z) : bool :=
  Z.leb threshold n_signers.

Lemma valid_threshold_correct : forall threshold n_signers,
  0 < threshold -> 0 < n_signers ->
  valid_threshold_model threshold n_signers =
    bool_decide (threshold <= n_signers).
Proof.
  intros threshold n_signers Ht Hn.
  unfold valid_threshold_model.
  destruct (Z.leb threshold n_signers) eqn:Hle.
  - apply Z.leb_le in Hle.
    case_bool_decide; [reflexivity | lia].
  - apply Z.leb_gt in Hle.
    case_bool_decide; [lia | reflexivity].
Qed.

(** Key property: valid threshold is monotonic in n_signers *)
Theorem valid_threshold_monotonic : forall threshold n1 n2,
  0 < threshold -> 0 < n1 -> n1 <= n2 ->
  valid_threshold_model threshold n1 = true ->
  valid_threshold_model threshold n2 = true.
Proof.
  intros threshold n1 n2 Ht Hn1 Hle Hvalid.
  unfold valid_threshold_model in *.
  apply Z.leb_le in Hvalid.
  apply Z.leb_le. lia.
Qed.

(** Key property: threshold 1 is always valid *)
Theorem threshold_one_valid : forall n_signers,
  0 < n_signers ->
  valid_threshold_model 1 n_signers = true.
Proof.
  intros n_signers Hn.
  unfold valid_threshold_model.
  apply Z.leb_le. lia.
Qed.

(** Key property: threshold > n_signers is invalid *)
Theorem threshold_too_high_invalid : forall threshold n_signers,
  0 < threshold -> 0 < n_signers ->
  n_signers < threshold ->
  valid_threshold_model threshold n_signers = false.
Proof.
  intros threshold n_signers Ht Hn Hgt.
  unfold valid_threshold_model.
  apply Z.leb_gt. lia.
Qed.

Close Scope Z_scope.

End proof.
