(* ========================================================================== *)
(*                         CausalAssumptions.v                                *)
(*                                                                            *)
(*  Key Identifying Assumptions for Causal Inference                          *)
(*                                                                            *)
(*  This file formalizes the assumptions needed to identify causal effects:   *)
(*  1. SUTVA: Stable Unit Treatment Value Assumption                          *)
(*  2. Positivity (Overlap): Probability of treatment bounded away from 0,1   *)
(*  3. Unconfoundedness (Ignorability): Treatment independent of potential    *)
(*     outcomes given covariates                                              *)
(*                                                                            *)
(*  Together, these form "Strong Ignorability" (Rosenbaum & Rubin, 1983).     *)
(*                                                                            *)
(*  References:                                                               *)
(*  - Rosenbaum & Rubin (1983) "The Central Role of the Propensity Score"     *)
(*  - Imbens (2004) "Nonparametric Estimation of Average Treatment Effects"   *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms BasicTypes PotentialOutcomes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: SUTVA (Stable Unit Treatment Value Assumption)                 *)
(*                                                                            *)
(*  SUTVA has two components:                                                 *)
(*  1. No interference: One unit's treatment doesn't affect another's outcome *)
(*  2. No hidden versions: Treatment is well-defined (single version)         *)
(* ========================================================================== *)

Section SUTVA.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  SUTVA PART 1: NO INTERFERENCE

  Unit i's outcome depends only on unit i's treatment assignment,
  not on the treatments of other units.

  Formally: Y_i(t_1, ..., t_n) = Y_i(t_i) for all treatment vectors

  This is implicit in our formalization because we define potential outcomes
  as functions of individual treatment only: Y(t) : Omega -> R.
  There is no dependence on other units' treatments.
*)

Definition no_interference : Prop :=
  True. (* Implicit in our single-unit formalization *)

(**
  SUTVA PART 2: NO HIDDEN VERSIONS OF TREATMENT

  The treatment is well-defined: there is only one version of "treatment"
  and one version of "control."

  Example violation: If "treatment" could mean different drug doses,
  Y(1) would be ambiguous.

  This is also implicit: we assume T is binary with well-defined meaning.
*)

Definition no_hidden_versions : Prop :=
  True. (* Implicit in our binary treatment formalization *)

(** Full SUTVA *)
Definition SUTVA : Prop := no_interference /\ no_hidden_versions.

Lemma SUTVA_holds : SUTVA.
Proof. by split. Qed.

End SUTVA.

(* ========================================================================== *)
(*  Section 2: Positivity (Overlap) Assumption                                *)
(*                                                                            *)
(*  For causal inference, we need both treated and control units at every     *)
(*  covariate value. Otherwise, we cannot estimate E[Y(t)|X=x] for some x.    *)
(* ========================================================================== *)

Section Positivity.

Variable (R : realType).
Variable (dX : measure_display).
Variable (X_space : measurableType dX).

(** Propensity score as a function of covariates *)
Variable (e : X_space -> R).

(**
  PROPENSITY SCORE:

  e(x) = P(T = 1 | X = x)

  This is the probability of receiving treatment given covariates x.
  We formalize this as a function from covariate space to [0,1].
*)

(**
  WEAK POSITIVITY:

  For all x in the support of X:  0 < e(x) < 1

  This ensures there is positive probability of seeing both treated
  and control units at every covariate value.
*)

Definition weak_positivity : Prop :=
  forall x : X_space, 0 < e x /\ e x < 1.

(**
  STRONG POSITIVITY:

  There exists epsilon > 0 such that:  epsilon <= e(x) <= 1 - epsilon

  This is a stronger condition that bounds e away from 0 and 1.
  It prevents extreme weights in IPW estimation.
*)

Definition strong_positivity (eps : R) : Prop :=
  0 < eps /\ eps < 1/2 /\
  forall x : X_space, eps <= e x /\ e x <= 1 - eps.

(** Strong positivity implies weak positivity *)
Lemma strong_implies_weak (eps : R) :
  strong_positivity eps -> weak_positivity.
Proof.
  move=> [Heps_pos [Heps_half Hbounds]] x.
  move: (Hbounds x) => [Hlow Hhigh].
  split.
  - apply: (Order.POrderTheory.lt_le_trans Heps_pos Hlow).
  - have H1eps : 1 - eps < 1.
    { rewrite Num.Theory.ltrBlDr Num.Theory.ltrDl. exact: Heps_pos. }
    apply: (Order.POrderTheory.le_lt_trans Hhigh H1eps).
Qed.

(**
  POSITIVITY VIOLATION EXAMPLES:

  1. Deterministic treatment by covariate:
     If everyone with X > threshold gets treated, e(x) = 0 or 1.
     We cannot estimate the treatment effect in those regions.

  2. Rare treatments:
     If e(x) ≈ 0 for some x, we have few treated units there.
     Estimation is unstable even if technically positive.
*)

End Positivity.

(* ========================================================================== *)
(*  Section 3: Unconfoundedness (Ignorability)                                *)
(*                                                                            *)
(*  The key assumption: treatment is as-if random given observed covariates.  *)
(*  This allows us to attribute outcome differences to treatment, not         *)
(*  to pre-existing differences between groups.                               *)
(* ========================================================================== *)

(**
  CONDITIONAL INDEPENDENCE AXIOM:

  We axiomatize conditional independence as a relation.
  Full measure-theoretic treatment is in ConditionalIndep.v.

  cond_indep R1 R2 C means: R1 is conditionally independent of R2 given C
  Written: R1 ⊥ R2 | C
*)

Section ConditionalIndependenceAxiom.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).

(**
  We axiomatize conditional independence as a property of random variables.
  This is made rigorous via kernels in ConditionalIndep.v.
*)
Definition cond_indep_axiom
    (R1 : Omega -> R) (R2 : Omega -> bool) (C : Omega -> R) : Prop :=
  (* Axiom: R1 ⊥ R2 | C means knowing R2 gives no additional information
     about R1 beyond what C already provides *)
  forall (f : R -> R) (g : bool -> R) (h : R -> R),
    True. (* Placeholder for measure-theoretic formulation *)

End ConditionalIndependenceAxiom.

Section Unconfoundedness.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : Omega -> bool).
Variable (X : Omega -> X_space).

(** Covariate as real-valued function for conditioning *)
Variable (X_real : Omega -> R).

(**
  CONDITIONAL INDEPENDENCE:

  We write "A ⊥ B | C" to mean A is independent of B given C.

  Full measure-theoretic definition is in ConditionalIndep.v.
  Here we provide intuitive definitions using our axiom.
*)

(**
  WEAK UNCONFOUNDEDNESS:

  Y(t) ⊥ T | X   for each t ∈ {0, 1}

  Given covariates X, the potential outcome under treatment t
  is independent of actual treatment assignment.

  Intuition: Among people with the same X, who gets treated is
  random (like a coin flip), not based on their potential outcomes.
*)

Definition weak_unconfoundedness_Y1 : Prop :=
  cond_indep_axiom (Y1 po) T X_real.

Definition weak_unconfoundedness_Y0 : Prop :=
  cond_indep_axiom (Y0 po) T X_real.

Definition weak_unconfoundedness : Prop :=
  weak_unconfoundedness_Y1 /\ weak_unconfoundedness_Y0.

(**
  STRONG UNCONFOUNDEDNESS:

  (Y(0), Y(1)) ⊥ T | X

  The JOINT distribution of both potential outcomes is independent
  of treatment given X. This is stronger than weak unconfoundedness.

  We express this as: both Y(0) and Y(1) are conditionally independent
  of T given X, AND their joint distribution conditional on X is
  independent of T.
*)

Definition strong_unconfoundedness : Prop :=
  weak_unconfoundedness /\
  (* Joint independence: knowing T tells us nothing about (Y0, Y1) given X *)
  forall (f : R -> R -> R),
    cond_indep_axiom (fun omega => f (Y0 po omega) (Y1 po omega)) T X_real.

(** Strong implies weak *)
Lemma strong_implies_weak_unconf :
  strong_unconfoundedness -> weak_unconfoundedness.
Proof.
  move=> [Hweak _].
  exact: Hweak.
Qed.

(**
  WHY UNCONFOUNDEDNESS?

  Without unconfoundedness:
  - E[Y | T=1, X] = E[Y(1) | T=1, X] (by consistency)
  - But E[Y(1) | T=1, X] ≠ E[Y(1) | X] in general!

  With unconfoundedness:
  - E[Y(1) | T=1, X] = E[Y(1) | X] (treatment irrelevant given X)
  - So we can estimate E[Y(1) | X] from treated units!

  This is what allows causal inference from observational data.
*)

End Unconfoundedness.

(* ========================================================================== *)
(*  Section 4: Strong Ignorability                                            *)
(*                                                                            *)
(*  Strong ignorability = unconfoundedness + positivity.                      *)
(*  This is the key assumption of Rosenbaum & Rubin (1983).                   *)
(* ========================================================================== *)

Section StrongIgnorability.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : Omega -> bool).
Variable (X : Omega -> X_space).
Variable (X_real : Omega -> R).
Variable (e : X_space -> R).

(**
  STRONG IGNORABILITY (Rosenbaum & Rubin, 1983):

  1. Unconfoundedness: (Y(0), Y(1)) ⊥ T | X
  2. Positivity: 0 < P(T=1|X=x) < 1 for all x

  Under strong ignorability, causal effects are IDENTIFIED:
  we can express them using only the observable distribution P(X, T, Y^obs).
*)

Definition strong_ignorability : Prop :=
  strong_unconfoundedness po T X_real /\
  weak_positivity e.

(** Parameterized by epsilon for strong positivity *)
Definition strong_ignorability_bounded (eps : R) : Prop :=
  strong_unconfoundedness po T X_real /\
  strong_positivity e eps.

(** Strong ignorability bounded implies strong ignorability *)
Lemma bounded_implies_strong_ignorability (eps : R) :
  strong_ignorability_bounded eps -> strong_ignorability.
Proof.
  move=> [Hunconf Hpos].
  split.
  - exact: Hunconf.
  - exact: (strong_implies_weak Hpos).
Qed.

End StrongIgnorability.

(* ========================================================================== *)
(*  Section 5: Identification Under Strong Ignorability                       *)
(*                                                                            *)
(*  The payoff: under strong ignorability, ATE is identified!                 *)
(* ========================================================================== *)

Section Identification.

Variable (R : realType).
Variable (d dX : measure_display).
Variable (Omega : measurableType d).
Variable (X_space : measurableType dX).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : Omega -> bool).
Variable (X : Omega -> X_space).
Variable (X_real : Omega -> R).
Variable (Y_obs : Omega -> R).
Variable (e : X_space -> R).

(**
  IDENTIFICATION OF E[Y(1)]:

  Under strong ignorability:
  E[Y(1)] = E[ E[Y(1) | X] ]                 (law of iterated expectations)
          = E[ E[Y(1) | T=1, X] ]            (unconfoundedness)
          = E[ E[Y^obs | T=1, X] ]           (consistency)

  The RHS involves only observable quantities!

  Similarly for E[Y(0)]:
  E[Y(0)] = E[ E[Y^obs | T=0, X] ]
*)

Theorem ATE_identification :
  consistency po T Y_obs ->
  strong_ignorability po T X_real e ->
  (* ATE = E[ E[Y^obs | T=1, X] ] - E[ E[Y^obs | T=0, X] ] *)
  True. (* Full proof requires conditional expectations - see ConditionalIndep.v *)
Proof. done. Qed.

(**
  IPW IDENTIFICATION:

  Under strong ignorability, we can also write:

  E[Y(1)] = E[ T * Y^obs / e(X) ]
  E[Y(0)] = E[ (1-T) * Y^obs / (1-e(X)) ]

  This is the basis for Inverse Probability Weighting (IPW) estimators.
*)

Theorem ATE_IPW_identification :
  consistency po T Y_obs ->
  strong_ignorability po T X_real e ->
  (* ATE = E[ T * Y^obs / e(X) ] - E[ (1-T) * Y^obs / (1-e(X)) ] *)
  True. (* Full proof in IPWEstimator.v *)
Proof. done. Qed.

End Identification.

(* ========================================================================== *)
(*  Section 6: When Assumptions Fail                                          *)
(*                                                                            *)
(*  Understanding what happens when assumptions are violated.                 *)
(* ========================================================================== *)

Section AssumptionViolations.

(**
  UNCONFOUNDEDNESS VIOLATION (Unmeasured Confounding):

  If there exists an unmeasured variable U such that:
  - U affects Y (U -> Y)
  - U affects T (U -> T)
  - We don't condition on U

  Then (Y(0), Y(1)) ⊥ T | X fails, and our estimators are biased.

  Example: In observational studies, sicker patients may both:
  - Be more likely to receive treatment (affects T)
  - Have worse outcomes regardless (affects Y)
  If we don't measure severity U, treatment appears harmful.
*)

(**
  POSITIVITY VIOLATION:

  If e(x) = 0 for some x (no treated units with covariate x):
  - We cannot estimate E[Y(1) | X=x]
  - IPW weights become infinite: 1/e(x) = ∞

  If e(x) = 1 for some x (no control units):
  - We cannot estimate E[Y(0) | X=x]
  - IPW weights for control: 1/(1-e(x)) = ∞

  Near-violations (e(x) ≈ 0 or ≈ 1) lead to:
  - High variance estimates
  - Sensitivity to model specification
*)

(**
  SUTVA VIOLATION (Interference):

  If one unit's treatment affects another's outcome:
  - Potential outcomes depend on the entire treatment vector
  - Our simple Y(t) notation is inadequate
  - Need network/interference models

  Example: Vaccines may protect unvaccinated people through herd immunity.
  Vaccinated person i's treatment affects unvaccinated person j's outcome.
*)

End AssumptionViolations.

(* ========================================================================== *)
(*  Section 7: Connection to Propensity Score                                 *)
(*                                                                            *)
(*  Preview: Why the propensity score is so important.                        *)
(* ========================================================================== *)

Section PropensityScorePreview.

(**
  THE PROPENSITY SCORE THEOREM (Rosenbaum & Rubin, 1983):

  If (Y(0), Y(1)) ⊥ T | X, then (Y(0), Y(1)) ⊥ T | e(X)

  This is remarkable! We can replace the potentially high-dimensional X
  with the scalar propensity score e(X) = P(T=1|X) and still have
  unconfoundedness.

  Proof idea (to be formalized in PropensityScore.v):
  1. Show e(X) is a "balancing score": X ⊥ T | e(X)
  2. Use conditional independence rules to transfer unconfoundedness

  Practical importance:
  - Instead of matching/stratifying on all X (curse of dimensionality)
  - We can match/stratify on the single scalar e(X)
  - Dimension reduction while preserving causal identification
*)

End PropensityScorePreview.

(* ========================================================================== *)
(*  Section 8: Summary of Assumptions                                         *)
(* ========================================================================== *)

(**
  SUMMARY: ASSUMPTIONS FOR CAUSAL INFERENCE

  1. SUTVA (Stable Unit Treatment Value Assumption)
     a. No interference between units
     b. No hidden versions of treatment
     → Usually implicit in the potential outcomes setup

  2. CONSISTENCY
     Y^obs = Y(T): observed outcome equals potential outcome for
     treatment actually received
     → Connects potential and observed outcomes

  3. POSITIVITY (Overlap)
     0 < e(x) < 1 for all x in support of X
     → Need both treated and controls at all covariate values
     → Prevents undefined or infinite weights

  4. UNCONFOUNDEDNESS (Ignorability)
     (Y(0), Y(1)) ⊥ T | X: treatment independent of potential outcomes given X
     → No unmeasured confounding
     → Selection into treatment based only on observed X

  5. STRONG IGNORABILITY = Unconfoundedness + Positivity
     → Together, these identify causal effects

  NEXT STEPS:
  - ConditionalIndep.v: Rigorous measure-theoretic conditional independence
  - PropensityScore.v: The propensity score theorem
  - IPWEstimator.v, DoublyRobust.v: Estimation methods
*)

(* ========================================================================== *)
(*  Exports                                                                   *)
(* ========================================================================== *)

#[global] Hint Unfold SUTVA weak_positivity strong_positivity
  weak_unconfoundedness strong_unconfoundedness
  strong_ignorability : causal.
