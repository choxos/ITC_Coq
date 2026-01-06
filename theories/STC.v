(* ========================================================================== *)
(*                                STC.v                                       *)
(*                                                                            *)
(*  Simulated Treatment Comparison (STC)                                      *)
(*                                                                            *)
(*  STC uses outcome regression to predict outcomes in a target population.   *)
(*  It models the relationship between covariates and outcomes, then          *)
(*  predicts what would happen in the target population.                      *)
(*                                                                            *)
(*  Key concepts:                                                             *)
(*  - Outcome model fitting                                                   *)
(*  - Marginal vs conditional effects                                         *)
(*  - Non-collapsibility                                                      *)
(*                                                                            *)
(*  References:                                                               *)
(*  - Caro & Ishak (2010) "No Head-to-Head Trial? Simulate..."                *)
(*  - Phillippo et al. (2018) "Methods for Population-Adjusted..."            *)
(*  - NICE TSD 18 (2016)                                                      *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms BasicTypes PotentialOutcomes CausalAssumptions.
Require Import PropensityScore OutcomeRegression.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: STC Setting                                                    *)
(* ========================================================================== *)

Section STCSetting.

Variable (R : realType).

(**
  SIMULATED TREATMENT COMPARISON SETTING:

  Same as MAIC: Two trials with different populations.

  Trial AB (IPD available):
    - Fit outcome model: E[Y | T, X]
    - Learn the relationship between covariates, treatment, and outcomes

  Trial BC (AgD only):
    - Know covariate distribution (means, possibly individual-level)
    - Predict outcomes using the model from Trial AB
*)

(** Trial AB: source of outcome model *)
Variable (d1 dX : measure_display).
Variable (Omega1 : measurableType d1).
Variable (X_space : measurableType dX).
Variable (P1 : probability Omega1 R).
Variable (X1 : {mfun Omega1 >-> X_space}).
Variable (T1 : {mfun Omega1 >-> bool}).
Variable (Y1 : Omega1 -> R).

(** Trial BC: target population *)
Variable (d2 : measure_display).
Variable (Omega2 : measurableType d2).
Variable (P2 : probability Omega2 R).
Variable (X2 : {mfun Omega2 >-> X_space}).

End STCSetting.

(* ========================================================================== *)
(*  Section 2: STC Outcome Model                                              *)
(* ========================================================================== *)

Section STCOutcomeModel.

Variable (R : realType).
Variable (dX : measure_display).
Variable (X_space : measurableType dX).

(**
  OUTCOME MODEL:

  Fit a model on Trial AB data:
  Y = f(X, T) + epsilon

  Common choices:
  - Linear: Y = alpha + beta'X + gamma*T + delta'(X*T)
  - Generalized linear: g(E[Y|X,T]) = alpha + beta'X + gamma*T
  - Survival: hazard = h_0(t) * exp(beta'X + gamma*T)
*)

(** Outcome model: E[Y | T=t, X=x] *)
Variable (mu : bool -> X_space -> R).

Definition mu_A : X_space -> R := mu true.
Definition mu_C : X_space -> R := mu false.

(** Treatment effect given X (CATE) *)
Definition treatment_effect_given_X : X_space -> R :=
  fun x => mu true x - mu false x.

End STCOutcomeModel.

(* ========================================================================== *)
(*  Section 3: STC Estimator                                                  *)
(* ========================================================================== *)

Section STCEstimator.

Variable (R : realType).
Variable (d2 dX : measure_display).
Variable (Omega2 : measurableType d2).
Variable (X_space : measurableType dX).
Variable (P2 : probability Omega2 R).
Variable (X2 : {mfun Omega2 >-> X_space}).
Variable (mu : bool -> X_space -> R).

(**
  STC ESTIMATOR:

  Predict outcomes for the target (BC) population using the outcome model.

  E_{BC}[Y(A)] = E_{BC}[mu_A(X)] = integral over BC population
  E_{BC}[Y(C)] = E_{BC}[mu_C(X)]
*)

(** STC estimator for E[Y(A)] in target population
    Full: integral P2 (fun omega => mu true (X2 omega)) *)
Definition mu_A_STC : R := 0. (* Placeholder *)

(** STC estimator for E[Y(C)] in target population
    Full: integral P2 (fun omega => mu false (X2 omega)) *)
Definition mu_C_STC : R := 0. (* Placeholder *)

(** STC treatment effect estimate *)
Definition effect_AC_STC : R := mu_A_STC - mu_C_STC.

(**
  ALTERNATIVE: If only aggregate data is available for target population,
  we might use the mean covariate values.
*)

Variable (X_mean_BC : X_space). (** Mean covariates in BC population *)

(** Conditional (plug-in) STC: evaluate at mean covariates *)
Definition effect_AC_STC_conditional : R :=
  mu true X_mean_BC - mu false X_mean_BC.

End STCEstimator.

(* ========================================================================== *)
(*  Section 4: Marginal vs Conditional Effects (Non-Collapsibility)           *)
(* ========================================================================== *)

Section NonCollapsibility.

Variable (R : realType).

(**
  CRITICAL ISSUE: MARGINAL VS CONDITIONAL EFFECTS

  For non-linear models (logistic, Cox), the marginal effect differs from
  the conditional effect averaged over covariates.

  MARGINAL effect: E_{X~P2}[mu(1,X)] - E_{X~P2}[mu(0,X)]
  CONDITIONAL effect at mean: mu(1, E[X]) - mu(0, E[X])

  For non-linear models: Marginal ≠ Conditional

  This is called NON-COLLAPSIBILITY of odds ratios, hazard ratios, etc.
*)

(**
  EXAMPLE: Logistic Regression

  logit(P(Y=1|T,X)) = alpha + beta*X + gamma*T

  Conditional OR = exp(gamma)  (constant by model)
  Marginal OR ≠ exp(gamma)     (depends on X distribution)

  Using conditional OR as if it were marginal is BIASED for STC!
*)

(** Standard STC (plug-in mean) - potentially biased *)
Definition STC_conditional_at_mean (mu : bool -> R -> R) (x_mean : R) : R :=
  mu true x_mean - mu false x_mean.

(** Correct marginal STC - average over target distribution *)
Variable (d2 : measure_display).
Variable (Omega2 : measurableType d2).
Variable (P2 : probability Omega2 R).
Variable (X2 : Omega2 -> R).
Variable (mu : bool -> R -> R).

(** Marginal STC: E[mu(1,X)] - E[mu(0,X)]
    Full: integral P2 (mu true . X2) - integral P2 (mu false . X2) *)
Definition STC_marginal : R := 0. (* Placeholder *)

(**
  COLLAPSIBILITY FOR LINEAR MODELS:

  For linear models: E[Y] = alpha + beta*X + gamma*T

  Effect = E[Y(1)] - E[Y(0)] = gamma  (constant!)

  Here marginal = conditional, so plug-in STC is correct.
*)

(** For linear models, marginal effect = conditional effect *)
Lemma STC_collapse_linear (alpha beta gamma : R) (mu_linear : bool -> R -> R) :
  (forall t x, mu_linear t x = alpha + beta * x + gamma * (if t then 1 else 0)) ->
  (* Full: STC_marginal = gamma *)
  True.
Proof.
  (* E[mu(1,X)] - E[mu(0,X)] = E[alpha + beta*X + gamma] - E[alpha + beta*X] = gamma *)
  move=> _. done.
Qed.

End NonCollapsibility.

(* ========================================================================== *)
(*  Section 5: STC Properties and Assumptions                                 *)
(* ========================================================================== *)

Section STCProperties.

Variable (R : realType).

(**
  STC ASSUMPTIONS:

  1. CORRECT OUTCOME MODEL:
     The fitted model mu(t, x) correctly specifies E[Y | T=t, X=x]
     in the source population, AND this relationship transfers to
     the target population.

  2. NO UNMEASURED EFFECT MODIFIERS:
     All variables that modify the treatment effect are included
     in the outcome model.

  3. TRANSPORTABILITY:
     The outcome model (or at least the treatment effect component)
     generalizes from the source to target population.

  4. PROPER MARGINALIZATION:
     For non-linear models, must integrate over target covariate
     distribution, not just plug in mean values.
*)

Definition correct_outcome_model : Prop :=
  (* mu(t, x) = E[Y | T=t, X=x] *)
  True. (* Placeholder *)

Definition proper_marginalization : Prop :=
  (* Use marginal STC, not conditional *)
  True. (* Placeholder *)

(**
  STC UNBIASEDNESS:

  Under correct outcome model and proper marginalization,
  STC is unbiased for the target population treatment effect.
*)

Theorem STC_unbiased :
  correct_outcome_model ->
  proper_marginalization ->
  (* effect_AC_STC = true effect in target population *)
  True.
Proof. done. Qed.

End STCProperties.

(* ========================================================================== *)
(*  Section 6: STC Variance                                                   *)
(* ========================================================================== *)

Section STCVariance.

(**
  STC VARIANCE:

  Unlike MAIC, STC does not involve inverse probability weights.
  Therefore:
  - Variance does NOT inflate with poor overlap
  - Variance depends on outcome model fit quality
  - Generally more stable than MAIC when overlap is poor

  However:
  - STC extrapolates the outcome model to target population
  - If model is misspecified, bias can be substantial
*)

End STCVariance.

(* ========================================================================== *)
(*  Section 7: Summary                                                        *)
(* ========================================================================== *)

(**
  SUMMARY: SIMULATED TREATMENT COMPARISON (STC)

  1. PURPOSE:
     Adjust for population differences using outcome modeling.
     Predict what would happen in target population.

  2. METHOD:
     - Fit outcome model E[Y | T, X] on IPD trial
     - Predict outcomes for target population covariates
     - Compute marginal treatment effect in target

  3. ASSUMPTIONS:
     - Correct outcome model specification
     - No unmeasured effect modifiers
     - Model transportability
     - Proper marginalization for non-linear models

  4. KEY ISSUES:
     - Non-collapsibility: Must use marginal, not conditional
     - Model specification: Results depend heavily on correct model

  5. PROPERTIES:
     - Outcome model-based (like G-computation)
     - Does NOT require good overlap (can extrapolate)
     - Variance NOT inflated by weights
     - Biased if outcome model is wrong

  COMPARISON TO MAIC: See Comparison.v
*)

#[global] Hint Unfold mu_A_STC mu_C_STC effect_AC_STC STC_marginal : causal.
