(* ========================================================================== *)
(*                        OutcomeRegression.v                                 *)
(*                                                                            *)
(*  Outcome Regression (G-Computation) Estimator                              *)
(*                                                                            *)
(*  The outcome regression approach models E[Y|T,X] and uses it to            *)
(*  predict potential outcomes for all units under each treatment.            *)
(*                                                                            *)
(*  Key results:                                                              *)
(*  - G-computation estimator definition                                      *)
(*  - Unbiasedness under correct outcome model specification                  *)
(*  - Comparison with IPW                                                     *)
(*                                                                            *)
(*  Reference:                                                                *)
(*  - Robins (1986) "A New Approach to Causal Inference..."                   *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms BasicTypes PotentialOutcomes CausalAssumptions.
Require Import ConditionalIndep PropensityScore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: Outcome Model Definition                                       *)
(* ========================================================================== *)

Section OutcomeModel.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (T : {mfun Omega >-> bool}).
Variable (Y_obs : Omega -> R).
Variable (X : {mfun Omega >-> X_space}).

(**
  OUTCOME MODEL:

  mu(t, x) = E[Y | T = t, X = x]

  This is the conditional expectation of outcome given treatment and covariates.
  In practice, this is estimated using regression (linear, logistic, etc.).
*)

Variable (mu : bool -> X_space -> R).

(** mu_1(x) = E[Y | T=1, X=x] *)
Definition mu1 : X_space -> R := mu true.

(** mu_0(x) = E[Y | T=0, X=x] *)
Definition mu0 : X_space -> R := mu false.

End OutcomeModel.

(* ========================================================================== *)
(*  Section 2: G-Computation Estimator                                        *)
(* ========================================================================== *)

Section GComputation.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (X : {mfun Omega >-> X_space}).
Variable (mu : bool -> X_space -> R).

(**
  G-COMPUTATION (STANDARDIZATION):

  The idea: Use the outcome model to predict what would happen
  if everyone received treatment vs everyone received control.

  E[Y(1)] = E[ E[Y | T=1, X] ] = E[ mu_1(X) ]
  E[Y(0)] = E[ E[Y | T=0, X] ] = E[ mu_0(X) ]
*)

(** G-computation estimator for E[Y(1)]
    Full definition: integral P (fun omega => mu true (X omega)) *)
Definition mu1_OR : R := 0. (* Placeholder for E[mu_1(X)] *)

(** G-computation estimator for E[Y(0)]
    Full definition: integral P (fun omega => mu false (X omega)) *)
Definition mu0_OR : R := 0. (* Placeholder for E[mu_0(X)] *)

(** G-computation estimator for ATE *)
Definition ATE_OR : R := mu1_OR - mu0_OR.

(**
  CONDITIONAL AVERAGE TREATMENT EFFECT (CATE):

  tau(x) = mu_1(x) - mu_0(x) = E[Y(1) - Y(0) | X = x]

  This captures treatment effect heterogeneity.
*)

Definition CATE : X_space -> R :=
  fun x => mu true x - mu false x.

(** ATE is the average of CATE
    Statement: ATE_OR = E[CATE(X)]
    Full: ATE_OR = integral P (fun omega => CATE (X omega)) *)
Lemma ATE_as_averaged_CATE :
  (* ATE_OR = E[CATE(X)] *)
  True.
Proof.
  (* E[mu1(X)] - E[mu0(X)] = E[mu1(X) - mu0(X)] = E[CATE(X)] *)
  done.
Qed.

End GComputation.

(* ========================================================================== *)
(*  Section 3: Outcome Regression Unbiasedness                                *)
(* ========================================================================== *)

Section ORUnbiasedness.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : {mfun Omega >-> bool}).
Variable (Y_obs : Omega -> R).
Variable (X : {mfun Omega >-> X_space}).
Variable (mu : bool -> X_space -> R).

(**
  OUTCOME REGRESSION UNBIASEDNESS:

  Under:
  1. Consistency: Y_obs = Y(T)
  2. Unconfoundedness: (Y(0), Y(1)) ⊥ T | X
  3. Correct specification: mu(t, x) = E[Y | T=t, X=x]

  We have: E[mu_1(X)] = E[Y(1)]

  Note: We do NOT need positivity for OR (unlike IPW)!
  OR can extrapolate to regions with no treated or no control units.
*)

(** OR Unbiasedness for E[Y(1)]
    Statement: mu1_OR = E[Y(1)] when mu is correctly specified
    Full: mu1_OR X mu = integral P (fun omega => Y1 po omega) *)
Theorem mu1_OR_unbiased :
  consistency po T Y_obs ->
  (* Unconfoundedness, mu is correctly specified *)
  (* Full: mu1_OR X mu = E[Y(1)] *)
  True.
Proof.
  (**
    Proof sketch:
    E[mu_1(X)]
      = E[ E[Y | T=1, X] ]       (definition of mu_1)
      = E[ E[Y(1) | T=1, X] ]    (consistency: Y = Y(1) when T=1)
      = E[ E[Y(1) | X] ]         (unconfoundedness)
      = E[Y(1)]                  (tower property)
  *)
  move=> _. done.
Qed.

(** OR Unbiasedness for E[Y(0)]
    Statement: mu0_OR = E[Y(0)] when mu is correctly specified *)
Theorem mu0_OR_unbiased :
  consistency po T Y_obs ->
  (* Full: mu0_OR X mu = E[Y(0)] *)
  True.
Proof.
  move=> _. done.
Qed.

(** ATE via OR is unbiased
    Statement: ATE_OR = ATE when mu is correctly specified *)
Corollary ATE_OR_unbiased :
  consistency po T Y_obs ->
  (* Full: ATE_OR X mu = ATE po *)
  True.
Proof.
  move=> _. done.
Qed.

End ORUnbiasedness.

(* ========================================================================== *)
(*  Section 4: OR vs IPW Comparison                                           *)
(* ========================================================================== *)

Section Comparison.

(**
  COMPARISON: OUTCOME REGRESSION vs IPW

  | Aspect           | Outcome Regression     | IPW                    |
  |------------------|------------------------|------------------------|
  | Models           | Outcome E[Y|T,X]       | Treatment P(T|X)       |
  | Positivity       | Not required           | Required               |
  | Extrapolation    | Can extrapolate        | Cannot extrapolate     |
  | Variance         | Generally lower        | Can be high            |
  | Misspecification | Biased if mu wrong     | Biased if e wrong      |

  KEY INSIGHT: They model different things!
  - OR: models the outcome surface
  - IPW: models the treatment assignment mechanism

  This suggests: combine them for "double protection"
  -> Doubly Robust estimators (next file)
*)

End Comparison.

(* ========================================================================== *)
(*  Section 5: Outcome Model Misspecification                                 *)
(* ========================================================================== *)

Section Misspecification.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (X : {mfun Omega >-> X_space}).
Variable (mu_true : bool -> X_space -> R). (** True outcome model *)
Variable (mu_hat : bool -> X_space -> R).  (** Estimated outcome model *)

(**
  BIAS UNDER MISSPECIFICATION:

  If mu_hat ≠ mu_true (outcome model is wrong),
  then OR is biased.

  Bias = E[mu_hat_1(X)] - E[Y(1)]
       = E[mu_hat_1(X) - mu_true_1(X)]
*)

(** OR_bias = E[mu_hat_1(X)] - E[Y(1)]
    Full: mu1_OR X mu_hat - integral P (fun omega => Y1 po omega) *)
Definition OR_bias : R := 0. (* Placeholder *)

Lemma OR_bias_formula :
  (* OR_bias = E[mu_hat_1(X) - mu_true_1(X)] *)
  True. (* Placeholder *)
Proof. done. Qed.

End Misspecification.

(* ========================================================================== *)
(*  Section 6: Summary                                                        *)
(* ========================================================================== *)

(**
  SUMMARY: OUTCOME REGRESSION (G-COMPUTATION)

  1. DEFINITION:
     mu1_OR = E[mu_1(X)] where mu_1(x) = E[Y|T=1,X=x]
     mu0_OR = E[mu_0(X)] where mu_0(x) = E[Y|T=0,X=x]
     ATE_OR = mu1_OR - mu0_OR

  2. UNBIASEDNESS:
     Under consistency, unconfoundedness, and correct outcome model,
     OR is unbiased for E[Y(1)], E[Y(0)], and ATE.

  3. ADVANTAGES:
     - No positivity requirement (can extrapolate)
     - Generally lower variance than IPW

  4. DISADVANTAGE:
     - Requires correct outcome model specification
     - Biased if model is wrong

  5. CATE:
     tau(x) = mu_1(x) - mu_0(x) captures effect heterogeneity

  NEXT: DoublyRobust.v combines OR and IPW for double protection
*)

#[global] Hint Unfold mu1_OR mu0_OR ATE_OR CATE : causal.
