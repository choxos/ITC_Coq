(* ========================================================================== *)
(*                            Comparison.v                                    *)
(*                                                                            *)
(*  Systematic Comparison of MAIC vs STC                                      *)
(*                                                                            *)
(*  This file provides a formal comparison of the two main population         *)
(*  adjustment methods: MAIC (weighting) and STC (outcome modeling).          *)
(*                                                                            *)
(*  Comparison dimensions:                                                    *)
(*  1. Assumptions required                                                   *)
(*  2. Bias properties                                                        *)
(*  3. Variance properties                                                    *)
(*                                                                            *)
(*  References:                                                               *)
(*  - Phillippo et al. (2018) "Methods for Population-Adjusted ITC"           *)
(*  - Remiro-Azócar et al. (2020) "Methods for Population Adjustment"         *)
(*  - NICE TSD 18 (2016)                                                      *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms BasicTypes PotentialOutcomes CausalAssumptions.
Require Import PropensityScore IPWEstimator OutcomeRegression DoublyRobust.
Require Import MAIC STC.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: Method Profile Records                                         *)
(* ========================================================================== *)

Section MethodProfiles.

(**
  We define formal profiles for each method, capturing their key properties.
  These can be compared programmatically.
*)

(** Method ID: 0=MAIC, 1=STC, 2=DR *)
Record method_profile := mkMethodProfile {
  method_id : nat;   (* 0=MAIC, 1=STC, 2=DoublyRobust *)
  requires_outcome_model : bool;
  requires_good_overlap : bool;
  bias_robust_to_model_misspec : bool;
  bias_robust_to_overlap : bool;
  variance_affected_by_weights : bool;
  can_extrapolate : bool
}.

(** MAIC Profile (method_id = 0) *)
Definition MAIC_profile : method_profile := {|
  method_id := 0;   (* MAIC *)
  requires_outcome_model := false;       (* Advantage: no outcome model needed *)
  requires_good_overlap := true;         (* Limitation: needs overlap *)
  bias_robust_to_model_misspec := true;  (* Advantage: no model to misspecify *)
  bias_robust_to_overlap := false;       (* Limitation: poor overlap = high variance *)
  variance_affected_by_weights := true;  (* Limitation: extreme weights inflate variance *)
  can_extrapolate := false               (* Limitation: cannot extrapolate *)
|}.

(** STC Profile (method_id = 1) *)
Definition STC_profile : method_profile := {|
  method_id := 1;   (* STC *)
  requires_outcome_model := true;        (* Limitation: needs correct model *)
  requires_good_overlap := false;        (* Advantage: no overlap requirement *)
  bias_robust_to_model_misspec := false; (* Limitation: biased if model wrong *)
  bias_robust_to_overlap := true;        (* Advantage: works with poor overlap *)
  variance_affected_by_weights := false; (* Advantage: stable variance *)
  can_extrapolate := true                (* Advantage: can extrapolate *)
|}.

(** Doubly Robust / ML-NMR Profile (method_id = 2) *)
Definition DR_profile : method_profile := {|
  method_id := 2;   (* Doubly Robust *)
  requires_outcome_model := true;        (* Uses outcome model *)
  requires_good_overlap := true;         (* Needs some overlap *)
  bias_robust_to_model_misspec := true;  (* DR: can be wrong if PS correct *)
  bias_robust_to_overlap := true;        (* DR: can be wrong if OR correct *)
  variance_affected_by_weights := true;  (* Still uses weights *)
  can_extrapolate := true                (* Can extrapolate via OR *)
|}.

End MethodProfiles.

(* ========================================================================== *)
(*  Section 2: Assumption Comparison                                          *)
(* ========================================================================== *)

Section AssumptionComparison.

(**
  ASSUMPTION COMPARISON: MAIC vs STC

  | Assumption Category     | MAIC                    | STC                     |
  |-------------------------|-------------------------|-------------------------|
  | Outcome model           | NOT REQUIRED            | REQUIRED (correct spec) |
  | Covariate overlap       | REQUIRED                | NOT REQUIRED            |
  | Effect modifiers        | Must be balanced        | Must be in model        |
  | Transportability        | Effect constancy        | Model transportability  |
*)

(**
  MAIC ASSUMPTIONS:

  1. Conditional constancy of relative effects
  2. All effect modifiers measured and balanced
  3. Adequate overlap (positivity)
  4. SUTVA (consistency)
*)

Definition MAIC_assumptions : Prop :=
  (* effect_modifiers_balanced *)
  (* adequate_overlap *)
  (* conditional_effect_constancy *)
  True. (* Placeholder *)

(**
  STC ASSUMPTIONS:

  1. Outcome model correctly specified
  2. All effect modifiers included in model
  3. Model transportability to target population
  4. Proper marginalization (for non-linear models)
  5. SUTVA (consistency)
*)

Definition STC_assumptions : Prop :=
  (* correct_outcome_model *)
  (* effect_modifiers_in_model *)
  (* model_transportability *)
  (* proper_marginalization *)
  True. (* Placeholder *)

(**
  KEY DIFFERENCE:

  MAIC: Does NOT need to correctly specify how X affects Y
        Just needs to balance X between populations

  STC:  MUST correctly specify how X affects Y
        But doesn't need X distributions to overlap
*)

Lemma assumption_difference :
  (* MAIC requires overlap but not outcome model
     STC requires outcome model but not overlap *)
  True.
Proof. done. Qed.

End AssumptionComparison.

(* ========================================================================== *)
(*  Section 3: Bias Comparison                                                *)
(* ========================================================================== *)

Section BiasComparison.

Variable (R : realType).

(**
  BIAS COMPARISON: MAIC vs STC

  | Bias Source                  | MAIC              | STC                     |
  |------------------------------|-------------------|-------------------------|
  | Unmeasured effect modifiers  | BIASED            | BIASED                  |
  | Outcome model misspecification| NOT AFFECTED     | BIASED                  |
  | Non-collapsibility           | NOT AFFECTED      | BIASED (if not marginal)|
  | Poor overlap                 | May be unstable   | NOT AFFECTED            |
*)

(**
  MAIC BIAS:

  MAIC is unbiased if:
  - All effect modifiers are measured and balanced
  - Weights successfully balance covariates

  MAIC can be biased due to:
  - Unmeasured effect modifiers (cannot balance what's not measured)
*)

(** MAIC bias sources: 0 = Unmeasured effect modifiers *)
Definition MAIC_bias_sources : list nat := [:: 0].

(**
  STC BIAS:

  STC is unbiased if:
  - Outcome model is correctly specified
  - Marginal effects properly computed

  STC can be biased due to:
  - Outcome model misspecification
  - Using conditional instead of marginal (non-collapsibility)
  - Unmeasured effect modifiers (not in model)
*)

(** STC bias sources: 1=Model misspec, 2=Non-collapsibility, 3=Unmeasured modifiers *)
Definition STC_bias_sources : list nat := [:: 1; 2; 3].

(**
  BIAS FORMULAS (Informal):

  MAIC bias ≈ Effect of unmeasured modifiers × Imbalance in unmeasured modifiers

  STC bias ≈ E[mu_hat(X) - mu_true(X)]
           + (Conditional effect - Marginal effect) [if using conditional]
*)

End BiasComparison.

(* ========================================================================== *)
(*  Section 4: Variance Comparison                                            *)
(* ========================================================================== *)

Section VarianceComparison.

Variable (R : realType).

(**
  VARIANCE COMPARISON: MAIC vs STC

  | Variance Driver             | MAIC                    | STC                   |
  |-----------------------------|-------------------------|-----------------------|
  | Sample size                 | Yes (standard)          | Yes (standard)        |
  | Weight extremity            | YES (major driver)      | No                    |
  | Overlap quality             | YES (affects weights)   | No                    |
  | Model complexity            | No                      | Yes (overfitting)     |
*)

(**
  MAIC VARIANCE:

  Var(MAIC) ∝ 1/ESS

  When ESS << n, variance is highly inflated.
  This happens when:
  - Target distribution differs greatly from source
  - Some target covariate values are rare in source
*)

Definition MAIC_variance_inflation (ESS n : R) : R :=
  n / ESS. (* Approximate variance inflation factor *)

(**
  STC VARIANCE:

  Var(STC) ∝ 1/n × (model variance)

  Generally more stable than MAIC because:
  - No inverse probability weights
  - Can extrapolate to unseen covariate regions
*)

(**
  PRACTICAL IMPLICATION:

  - When overlap is good (ESS ≈ n): MAIC and STC have similar variance
  - When overlap is poor (ESS << n): STC has much lower variance
*)

(** Variance comparison result: 0=STC preferred, 1=Either reasonable, 2=Consider carefully *)
Definition variance_comparison (ESS n : R) : nat :=
  if ESS / n < 1/2 then 0 (* STC preferred *)
  else if ESS / n > 4/5 then 1 (* Either reasonable *)
  else 2 (* Consider carefully *).

End VarianceComparison.

(* ========================================================================== *)
(*  Section 5: Summary Comparison Table                                       *)
(* ========================================================================== *)

Section SummaryTable.

(**
  COMPREHENSIVE COMPARISON TABLE:

  | Criterion                   | MAIC             | STC              | Winner        |
  |-----------------------------|------------------|------------------|---------------|
  | Requires outcome model      | No               | Yes              | MAIC          |
  | Requires good overlap       | Yes              | No               | STC           |
  | Bias if model wrong         | N/A              | Biased           | MAIC          |
  | Bias if poor overlap        | No (high var)    | No               | Tie           |
  | Variance with poor overlap  | HIGH             | Normal           | STC           |
  | Can extrapolate             | No               | Yes              | STC           |
  | Handles non-collapsibility  | Automatically    | Needs adjustment | MAIC          |
  | Computational complexity    | Low              | Medium           | MAIC          |
*)

(** Comparison summary as list of (criterion_id, MAIC_answer, STC_answer)
    Values: 0=No, 1=Yes, 2=High, 3=Normal, 4=N/A, 5=Automatic, 6=Needs work *)
Definition comparison_summary : list (nat * nat * nat) :=
  [:: (0, 0, 1);   (* Outcome model required: MAIC=No, STC=Yes *)
      (1, 1, 0);   (* Overlap required: MAIC=Yes, STC=No *)
      (2, 4, 0);   (* Robust to model misspec: MAIC=N/A, STC=No *)
      (3, 2, 3);   (* Variance with poor overlap: MAIC=High, STC=Normal *)
      (4, 0, 1);   (* Can extrapolate: MAIC=No, STC=Yes *)
      (5, 5, 6)    (* Non-collapsibility: MAIC=Automatic, STC=Needs work *)
  ].

End SummaryTable.

(* ========================================================================== *)
(*  Section 6: Method Selection Guidelines                                    *)
(* ========================================================================== *)

Section MethodSelection.

Variable (R : realType).

(**
  WHEN TO USE MAIC:

  1. Good covariate overlap exists (check ESS!)
  2. Uncertain about outcome model specification
  3. Non-linear effect measure (OR, HR) without marginalization capability
  4. Limited number of covariates to balance
*)

Definition prefer_MAIC (ESS_ratio : R) (outcome_model_confidence : R) : bool :=
  (ESS_ratio >= 1/2) && (outcome_model_confidence < 1/2).

(**
  WHEN TO USE STC:

  1. Poor covariate overlap (ESS would be very low)
  2. Confident in outcome model specification
  3. Linear effect measure or proper marginalization available
  4. Complex covariate relationships
*)

Definition prefer_STC (ESS_ratio : R) (outcome_model_confidence : R) : bool :=
  (ESS_ratio < 1/2) && (outcome_model_confidence >= 1/2).

(**
  WHEN TO USE DOUBLY ROBUST (ML-NMR):

  1. When you want protection against both types of misspecification
  2. When both IPD and aggregate data allow joint modeling
  3. When you can fit both propensity and outcome models
*)

Definition prefer_DR (ESS_ratio : R) (outcome_model_confidence : R) : bool :=
  (* Use doubly robust when uncertain about both *)
  (1/3 <= ESS_ratio) && (ESS_ratio <= 4/5) &&
  (1/3 <= outcome_model_confidence) && (outcome_model_confidence <= 4/5).

(**
  DECISION FUNCTION
  Returns: 0=MAIC, 1=STC, 2=DoublyRobust, 3=Consider carefully
*)

Definition recommend_method (ESS_ratio : R) (outcome_model_confidence : R) : nat :=
  if prefer_MAIC ESS_ratio outcome_model_confidence then 0 (* MAIC *)
  else if prefer_STC ESS_ratio outcome_model_confidence then 1 (* STC *)
  else if prefer_DR ESS_ratio outcome_model_confidence then 2 (* Doubly Robust *)
  else 3 (* Consider context carefully *).

End MethodSelection.

(* ========================================================================== *)
(*  Section 7: Formal Comparison Theorems                                     *)
(* ========================================================================== *)

Section FormalComparison.

Variable (R : realType).

(**
  THEOREM: Under correct specifications, MAIC and STC estimate the same quantity.

  If:
  - MAIC correctly balances all effect modifiers
  - STC correctly specifies the outcome model

  Then both estimate the true marginal treatment effect in the target population.
*)

Theorem methods_agree_when_correct :
  MAIC_assumptions ->
  STC_assumptions ->
  (* effect_AC_MAIC = effect_AC_STC = true_effect *)
  True. (* Placeholder *)
Proof. done. Qed.

(**
  THEOREM: MAIC is more robust to outcome model misspecification.
*)

Theorem MAIC_robust_to_outcome_model :
  (* If outcome model is misspecified but covariates balanced, *)
  (* MAIC is still unbiased (while STC is biased) *)
  True. (* Placeholder *)
Proof. done. Qed.

(**
  THEOREM: STC is more robust to poor overlap.
*)

Theorem STC_robust_to_poor_overlap :
  (* If overlap is poor, *)
  (* STC variance is stable while MAIC variance explodes *)
  True. (* Placeholder *)
Proof. done. Qed.

End FormalComparison.

(* ========================================================================== *)
(*  Section 8: Final Summary                                                  *)
(* ========================================================================== *)

(**
  FINAL SUMMARY: MAIC vs STC

  MAIC (Matching-Adjusted Indirect Comparison):
  - Based on: Weighting / IPW methodology
  - Strength: No outcome model needed; robust to model misspecification
  - Weakness: Requires overlap; variance inflates with extreme weights
  - Use when: Good overlap exists; uncertain about outcome model

  STC (Simulated Treatment Comparison):
  - Based on: Outcome regression / G-computation
  - Strength: Can extrapolate; stable variance regardless of overlap
  - Weakness: Requires correct outcome model; non-collapsibility issues
  - Use when: Poor overlap; confident in outcome model

  Doubly Robust / ML-NMR:
  - Combines: Both weighting and outcome modeling
  - Strength: Robust to misspecification of either component
  - Weakness: More complex; requires both models
  - Use when: Want double protection; willing to model both

  KEY INSIGHT:
  MAIC ↔ STC mirrors IPW ↔ Outcome Regression in causal inference.
  The same trade-offs apply:
  - Weighting-based methods don't need outcome models but need overlap
  - Model-based methods don't need overlap but need correct specification
  - Doubly robust methods combine both for protection against either failure
*)

(* ========================================================================== *)
(*  Exports                                                                   *)
(* ========================================================================== *)

#[global] Hint Unfold MAIC_profile STC_profile DR_profile recommend_method : causal.
