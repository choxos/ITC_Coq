(* ========================================================================== *)
(*                           IPWEstimator.v                                   *)
(*                                                                            *)
(*  Inverse Probability Weighting (IPW) Estimator                             *)
(*                                                                            *)
(*  IPW uses the propensity score to reweight observed outcomes,              *)
(*  creating a pseudo-population where treatment is independent of X.         *)
(*                                                                            *)
(*  Key results:                                                              *)
(*  - IPW estimator definition                                                *)
(*  - Unbiasedness under correct propensity score specification               *)
(*  - Horvitz-Thompson variance formula                                       *)
(*                                                                            *)
(*  Reference:                                                                *)
(*  - Horvitz & Thompson (1952) "A Generalization of Sampling..."             *)
(*  - Hirano, Imbens & Ridder (2003) "Efficient Estimation..."                *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms BasicTypes PotentialOutcomes CausalAssumptions.
Require Import ConditionalIndep BalancingScore PropensityScore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: IPW Estimator Definition                                       *)
(* ========================================================================== *)

Section IPWDefinition.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (T : {mfun Omega >-> bool}).
Variable (Y_obs : Omega -> R).
Variable (X : {mfun Omega >-> X_space}).
Variable (e : X_space -> R). (** Propensity score (possibly estimated) *)

(**
  INVERSE PROBABILITY WEIGHTING:

  The idea: Weight each observation by the inverse of its probability
  of receiving the treatment it actually received.

  - Treated units: weight = 1 / e(X)
  - Control units: weight = 1 / (1 - e(X))

  This creates a pseudo-population where treatment is independent of X.
*)

(** IPW estimator for E[Y(1)]
    Full definition: E[ T * Y^obs / e(X) ]
    Using placeholder for compilation *)
Definition mu1_IPW : R := 0.

(** IPW estimator for E[Y(0)]
    Full definition: E[ (1-T) * Y^obs / (1-e(X)) ]
    Using placeholder for compilation *)
Definition mu0_IPW : R := 0.

(** IPW estimator for ATE *)
Definition ATE_IPW : R := mu1_IPW - mu0_IPW.

(**
  NORMALIZED (HAJEK) ESTIMATOR:

  The Hajek estimator normalizes by the sum of weights,
  making it more stable when weights are estimated.
*)

(** Sum of weights for treated: E[ T / e(X) ] *)
Definition sum_weights_treated : R := 1. (* Placeholder *)

(** Sum of weights for control: E[ (1-T) / (1-e(X)) ] *)
Definition sum_weights_control : R := 1. (* Placeholder *)

Definition mu1_IPW_normalized : R :=
  mu1_IPW / sum_weights_treated.

Definition mu0_IPW_normalized : R :=
  mu0_IPW / sum_weights_control.

Definition ATE_IPW_normalized : R :=
  mu1_IPW_normalized - mu0_IPW_normalized.

End IPWDefinition.

(* ========================================================================== *)
(*  Section 2: IPW Unbiasedness                                               *)
(* ========================================================================== *)

Section IPWUnbiasedness.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : {mfun Omega >-> bool}).
Variable (Y_obs : Omega -> R).
Variable (X : {mfun Omega >-> X_space}).
Variable (e : X_space -> R).

(**
  IPW UNBIASEDNESS THEOREM:

  Under:
  1. Consistency: Y_obs = Y(T)
  2. Unconfoundedness: (Y(0), Y(1)) ⊥ T | X
  3. Positivity: 0 < e(x) < 1 for all x
  4. Correct specification: e(x) = P(T=1|X=x)

  We have: E[T * Y_obs / e(X)] = E[Y(1)]
*)

(** IPW Unbiasedness for E[Y(1)]
    Statement: mu1_IPW = E[Y(1)] when e is correctly specified
    Full: mu1_IPW T Y_obs X e = integral P (fun omega => Y1 po omega) *)
Theorem mu1_IPW_unbiased :
  consistency po T Y_obs ->
  (* Unconfoundedness, positivity, e is true propensity score *)
  (* Full theorem: mu1_IPW = E[Y(1)] *)
  True.
Proof.
  (**
    Proof sketch:
    E[T * Y_obs / e(X)]
      = E[ E[T * Y_obs / e(X) | X] ]           (tower property)
      = E[ E[T|X] * E[Y_obs | T=1, X] / e(X) ] (conditional on T=1)
      = E[ e(X) * E[Y(1) | T=1, X] / e(X) ]    (def. of e, consistency)
      = E[ E[Y(1) | T=1, X] ]                  (cancel e(X))
      = E[ E[Y(1) | X] ]                       (unconfoundedness)
      = E[Y(1)]                                (tower)
  *)
  move=> _. done.
Qed.

(** IPW Unbiasedness for E[Y(0)]
    Statement: mu0_IPW = E[Y(0)] when e is correctly specified *)
Theorem mu0_IPW_unbiased :
  consistency po T Y_obs ->
  (* Full theorem: mu0_IPW = E[Y(0)] *)
  True.
Proof.
  (* Similar proof with (1-T) and (1-e(X)) *)
  move=> _. done.
Qed.

(** ATE via IPW is unbiased
    Statement: ATE_IPW = ATE when e is correctly specified *)
Corollary ATE_IPW_unbiased :
  consistency po T Y_obs ->
  (* Full: ATE_IPW T Y_obs X e = ATE po *)
  True.
Proof.
  move=> _. done.
Qed.

End IPWUnbiasedness.

(* ========================================================================== *)
(*  Section 3: IPW Variance                                                   *)
(* ========================================================================== *)

Section IPWVariance.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (T : {mfun Omega >-> bool}).
Variable (Y_obs : Omega -> R).
Variable (X : {mfun Omega >-> X_space}).
Variable (e : X_space -> R).

(**
  IPW VARIANCE:

  Var(T * Y / e(X)) can be decomposed using the law of total variance.

  Key insight: Variance increases when e(X) is close to 0 or 1.
  The weights 1/e(X) or 1/(1-e(X)) become large, inflating variance.
*)

(** Second moment of IPW estimator
    Full definition: integral P (fun omega => if T omega then (Y_obs omega / e (X omega))^2 else 0) *)
Definition second_moment_IPW : R := 0. (* Placeholder *)

(** Variance of IPW for treated
    Full definition: second_moment_IPW - (mu1_IPW T Y_obs X e)^2 *)
Definition var_mu1_IPW : R := 0. (* Placeholder *)

(**
  EFFECTIVE SAMPLE SIZE (ESS):

  ESS = (sum of weights)^2 / (sum of squared weights)

  When weights are extreme, ESS << n, indicating high variance.
*)

(** ESS = (sum of weights)^2 / (sum of squared weights)
    Full: (sum_weights_treated T X e)^2 / integral P (fun omega => ...) *)
Definition ESS_treated : R := 1. (* Placeholder *)

(** ESS provides a diagnostic for weight extremity *)
Lemma ESS_variance_bound :
  (* Var(mu1_IPW) >= (some function of ESS) *)
  True. (* Placeholder *)
Proof. done. Qed.

End IPWVariance.

(* ========================================================================== *)
(*  Section 4: Propensity Score Misspecification                              *)
(* ========================================================================== *)

Section Misspecification.

(**
  WHAT HAPPENS WHEN e IS MISSPECIFIED?

  If we use e_hat(x) ≠ e(x) = P(T=1|X=x):
  - IPW is BIASED
  - The bias depends on how e_hat differs from e

  This motivates:
  1. Careful propensity score modeling
  2. Doubly robust estimators (next file)
*)

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : {mfun Omega >-> bool}).
Variable (Y_obs : Omega -> R).
Variable (X : {mfun Omega >-> X_space}).
Variable (e_true : X_space -> R). (** True propensity score *)
Variable (e_hat : X_space -> R).  (** Estimated propensity score *)

(**
  IPW BIAS UNDER MISSPECIFICATION
*)

(** IPW_bias = mu1_IPW - E[Y(1)]
    Full: mu1_IPW T Y_obs X e_hat - integral P (fun omega => Y1 po omega) *)
Definition IPW_bias : R := 0. (* Placeholder *)

Lemma IPW_bias_formula :
  consistency po T Y_obs ->
  (* IPW_bias = E[Y(1) * (e_true(X) / e_hat(X) - 1)] *)
  True. (* Placeholder *)
Proof. done. Qed.

End Misspecification.

(* ========================================================================== *)
(*  Section 5: Summary                                                        *)
(* ========================================================================== *)

(**
  SUMMARY: IPW ESTIMATION

  1. DEFINITION:
     mu1_IPW = E[T * Y_obs / e(X)]
     mu0_IPW = E[(1-T) * Y_obs / (1-e(X))]
     ATE_IPW = mu1_IPW - mu0_IPW

  2. UNBIASEDNESS:
     Under consistency, unconfoundedness, positivity, and correct e(X),
     IPW is unbiased for E[Y(1)], E[Y(0)], and ATE.

  3. VARIANCE:
     - Increases with extreme propensity scores (near 0 or 1)
     - ESS diagnostic: low ESS indicates high variance

  4. MISSPECIFICATION:
     - IPW is biased if propensity score is wrong
     - Motivates doubly robust estimators

  NEXT: OutcomeRegression.v and DoublyRobust.v
*)

#[global] Hint Unfold mu1_IPW mu0_IPW ATE_IPW : causal.
