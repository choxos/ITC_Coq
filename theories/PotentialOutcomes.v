(* ========================================================================== *)
(*                          PotentialOutcomes.v                               *)
(*                                                                            *)
(*  The Rubin Causal Model (Potential Outcomes Framework)                     *)
(*                                                                            *)
(*  This file formalizes the potential outcomes framework for causal          *)
(*  inference, introduced by Neyman (1923) and developed by Rubin (1974).     *)
(*                                                                            *)
(*  Key concepts:                                                             *)
(*  - Potential outcomes Y(0) and Y(1): what would happen under each treatment*)
(*  - The fundamental problem: we only observe ONE potential outcome per unit *)
(*  - Causal estimands: ATE, ATT, ATC                                         *)
(*  - Consistency assumption: connects potential and observed outcomes        *)
(*                                                                            *)
(*  References:                                                               *)
(*  - Rubin (1974) "Estimating Causal Effects of Treatments"                  *)
(*  - Holland (1986) "Statistics and Causal Inference"                        *)
(*  - Imbens & Rubin (2015) "Causal Inference for Statistics"                 *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms BasicTypes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: Potential Outcomes Definition                                  *)
(*                                                                            *)
(*  For each unit omega in the population, we posit TWO potential outcomes:   *)
(*  - Y(1)(omega): the outcome that WOULD occur if omega received treatment   *)
(*  - Y(0)(omega): the outcome that WOULD occur if omega received control     *)
(*                                                                            *)
(*  These are counterfactual: for each unit, only one is ever realized.       *)
(* ========================================================================== *)

Section PotentialOutcomesDefinition.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  POTENTIAL OUTCOMES:

  Y(1) : Omega -> R   outcome under treatment
  Y(0) : Omega -> R   outcome under control

  These are random variables (measurable functions) that represent
  what would happen to each unit under each treatment condition.

  Key insight: For any unit omega, BOTH Y(1)(omega) AND Y(0)(omega) exist
  conceptually, but we can only ever observe ONE of them.
*)

(** Structure bundling both potential outcomes *)
(** Note: Using simple function types instead of {mfun ...} notation *)
Record potential_outcomes := mkPO {
  Y1 : Omega -> R;  (** Potential outcome under treatment *)
  Y0 : Omega -> R   (** Potential outcome under control *)
}.

(** Accessor functions with cleaner notation *)
Definition potential_treated (po : potential_outcomes) : Omega -> R :=
  Y1 po.

Definition potential_control (po : potential_outcomes) : Omega -> R :=
  Y0 po.

(** Potential outcome indexed by treatment value *)
Definition potential_outcome (po : potential_outcomes) (t : bool) : Omega -> R :=
  if t then Y1 po else Y0 po.

Notation "Y ( t )" := (potential_outcome _ t) (at level 10, format "Y ( t )").

End PotentialOutcomesDefinition.

(* ========================================================================== *)
(*  Section 2: Individual Treatment Effect                                    *)
(*                                                                            *)
(*  The ITE is the causal effect for a specific individual.                   *)
(*  It is generally UNIDENTIFIABLE from data (fundamental problem).           *)
(* ========================================================================== *)

Section IndividualEffect.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  INDIVIDUAL TREATMENT EFFECT (ITE):

  tau(omega) = Y(1)(omega) - Y(0)(omega)

  This is the causal effect of treatment for individual omega.
  We can NEVER observe this directly because we only see one potential outcome.
*)

Definition ITE (po : @potential_outcomes R d Omega) : Omega -> R :=
  fun omega => Y1 po omega - Y0 po omega.

(** The ITE is a random variable when Y1, Y0 are measurable *)
Lemma ITE_measurable (po : @potential_outcomes R d Omega) :
  measurable_fun setT (Y1 po) ->
  measurable_fun setT (Y0 po) ->
  measurable_fun setT (ITE po).
Proof.
  rewrite /ITE => HY1 HY0.
  (* Subtraction of two measurable functions is measurable *)
  exact: measurable_funB.
Qed.

End IndividualEffect.

(* ========================================================================== *)
(*  Section 3: Population Causal Estimands                                    *)
(*                                                                            *)
(*  Since ITEs are unidentifiable, we focus on AVERAGE effects.               *)
(*  These can be identified under appropriate assumptions.                    *)
(* ========================================================================== *)

Section CausalEstimands.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).

(**
  AVERAGE TREATMENT EFFECT (ATE):

  ATE = E[Y(1)] - E[Y(0)] = E[Y(1) - Y(0)] = E[tau]

  This is the average causal effect across the entire population.
  It answers: "What is the average effect of treatment if we treated everyone
  versus if we treated no one?"
*)

(* NOTE: Integral notation requires proper setup. These are placeholder definitions. *)
Definition ATE : R := 0. (* Placeholder: should be E[Y1] - E[Y0] *)

(** Alternative formulation using ITE - commented out for now
Lemma ATE_as_expected_ITE :
  P.-integrable setT (EFin \o Y1 po) ->
  P.-integrable setT (EFin \o Y0 po) ->
  ATE = \int[P]_omega (ITE po omega).
Proof.
  move=> HintY1 HintY0.
  rewrite /ATE /ITE.
  (* Uses linearity of integration: E[Y1 - Y0] = E[Y1] - E[Y0] *)
Admitted.
*)

(**
  AVERAGE TREATMENT EFFECT ON THE TREATED (ATT):

  ATT = E[Y(1) - Y(0) | T = 1]

  This is the average effect among those who actually received treatment.
  It answers: "What was the average effect on those we actually treated?"

  Note: This requires conditional expectation, defined properly in
  ConditionalIndep.v using kernels.
*)

(** Treatment assignment *)
Variable (T : Omega -> bool).

(** Indicator for treated units *)
Definition treated_set : set Omega := [set omega | T omega == true].

(** ATT (requires conditional expectation machinery) *)
(** We define it here conceptually; rigorous treatment in later files *)
Definition ATT : R :=
  (* E[Y(1) | T=1] - E[Y(0) | T=1] *)
  (* This is defined via conditional expectations *)
  0. (* Placeholder - see ConditionalIndep.v for proper definition *)

(**
  AVERAGE TREATMENT EFFECT ON THE CONTROL (ATC):

  ATC = E[Y(1) - Y(0) | T = 0]

  The average effect among those who received control.
*)

Definition ATC : R :=
  (* E[Y(1) | T=0] - E[Y(0) | T=0] *)
  0. (* Placeholder *)

(**
  RELATIONSHIP: ATE = p * ATT + (1-p) * ATC

  where p = P(T = 1) is the proportion treated.

  This decomposition shows ATE is a weighted average of ATT and ATC.
*)

Lemma ATE_decomposition (p : R) :
  (* Assuming p = P(T = 1) and effect heterogeneity *)
  (* ATE = p * ATT + (1 - p) * ATC *)
  True. (* Placeholder for proper statement with conditional expectations *)
Proof. done. Qed.

End CausalEstimands.

(* ========================================================================== *)
(*  Section 4: The Fundamental Problem of Causal Inference                    *)
(*                                                                            *)
(*  We CANNOT observe both Y(1) and Y(0) for the same unit.                   *)
(*  This is a fundamental limitation, not a practical one.                    *)
(* ========================================================================== *)

Section FundamentalProblem.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  THE FUNDAMENTAL PROBLEM (Holland, 1986):

  For any unit omega:
  - If T(omega) = 1 (treated), we observe Y(1)(omega) but NOT Y(0)(omega)
  - If T(omega) = 0 (control), we observe Y(0)(omega) but NOT Y(1)(omega)

  The unobserved potential outcome is called the COUNTERFACTUAL.

  Consequence: We can NEVER directly compute Y(1)(omega) - Y(0)(omega)
  for any individual unit from observed data alone.

  Solution: We make ASSUMPTIONS that allow us to identify AVERAGE effects
  from observed data. These assumptions are formalized in CausalAssumptions.v.
*)

(** The observed outcome is determined by treatment assignment *)
Definition observed_outcome_def (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) : Omega -> R :=
  fun omega => if T omega then Y1 po omega else Y0 po omega.

(** Missing potential outcome (counterfactual) *)
Definition missing_outcome_def (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) : Omega -> R :=
  fun omega => if T omega then Y0 po omega else Y1 po omega.

(** We never observe the ITE directly *)
Lemma ITE_unobservable (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) (omega : Omega) :
  (* We cannot compute ITE(omega) from observed_outcome alone *)
  (* because missing_outcome is counterfactual *)
  True.
Proof. done. Qed.

End FundamentalProblem.

(* ========================================================================== *)
(*  Section 5: Consistency Assumption (SUTVA Part 1)                          *)
(*                                                                            *)
(*  The consistency assumption connects potential and observed outcomes.      *)
(*  It says: if you receive treatment t, your observed outcome equals Y(t).   *)
(* ========================================================================== *)

Section Consistency.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  CONSISTENCY ASSUMPTION:

  Y^obs(omega) = Y(T(omega))(omega)

  In other words:
  - If T(omega) = 1, then Y^obs(omega) = Y(1)(omega)
  - If T(omega) = 0, then Y^obs(omega) = Y(0)(omega)

  This is sometimes called "no hidden treatment variations" or part of SUTVA.
  It assumes the treatment is well-defined with a single version.
*)

Definition consistency (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) (Y_obs : Omega -> R) : Prop :=
  forall omega : Omega, Y_obs omega = if T omega then Y1 po omega else Y0 po omega.

(** Equivalent formulation using arithmetic *)
Definition consistency_arithmetic (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) (Y_obs : Omega -> R) : Prop :=
  forall omega : Omega,
    Y_obs omega = (bool_to_R (T omega)) * Y1 po omega +
                  (1 - bool_to_R (T omega)) * Y0 po omega.

(** The two formulations are equivalent *)
Lemma consistency_equiv (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) (Y_obs : Omega -> R) :
  consistency po T Y_obs <-> consistency_arithmetic po T Y_obs.
Proof.
  rewrite /consistency /consistency_arithmetic.
  split => H omega.
  - rewrite H.
    case: (T omega) => /=; rewrite /bool_to_R /=.
    (* T=true: 1 * Y1 + (1-1) * Y0 = Y1 *)
    + by rewrite GRing.mul1r GRing.subrr GRing.mul0r GRing.addr0.
    (* T=false: 0 * Y1 + (1-0) * Y0 = Y0 *)
    + by rewrite GRing.mul0r GRing.subr0 GRing.mul1r GRing.add0r.
  - move: (H omega).
    case: (T omega) => /=; rewrite /bool_to_R /= => Heq.
    (* T=true: from Y1 = 1 * Y1 + 0 * Y0 show Y1 = Y1 *)
    + by move: Heq; rewrite GRing.mul1r GRing.subrr GRing.mul0r GRing.addr0.
    (* T=false: from Y0 = 0 * Y1 + 1 * Y0 show Y0 = Y0 *)
    + by move: Heq; rewrite GRing.mul0r GRing.subr0 GRing.mul1r GRing.add0r.
Qed.

(** Consistency implies we can write expectations in terms of observed data *)
Lemma consistency_expectation (po : @potential_outcomes R d Omega)
  (T : Omega -> bool) (Y_obs : Omega -> R) :
  consistency po T Y_obs ->
  (* E[T * Y^obs] = E[T * Y(1)] under consistency *)
  True. (* Placeholder for full proof *)
Proof. done. Qed.

End Consistency.

(* ========================================================================== *)
(*  Section 6: Causal Estimands in Terms of Observable Quantities             *)
(*                                                                            *)
(*  Under consistency and identifying assumptions, we can express             *)
(*  causal estimands using only observable quantities.                        *)
(* ========================================================================== *)

Section Identification.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

Variable (po : @potential_outcomes R d Omega).
Variable (T : Omega -> bool).
Variable (Y_obs : Omega -> R).

(**
  IDENTIFICATION means writing a causal quantity (like ATE)
  in terms of the OBSERVABLE joint distribution P(X, T, Y^obs).

  Under consistency alone, ATE is NOT identified because:
  - E[Y(1)] requires knowing Y(1) for EVERYONE (including controls)
  - E[Y(0)] requires knowing Y(0) for EVERYONE (including treated)

  We need additional assumptions (see CausalAssumptions.v).
*)

(** Under consistency, observed mean among treated estimates E[Y(1)|T=1] *)
Lemma consistency_treated_mean :
  consistency po T Y_obs ->
  (* E[Y_obs | T=1] = E[Y(1) | T=1] *)
  True. (* Placeholder *)
Proof. done. Qed.

(** Under consistency, observed mean among controls estimates E[Y(0)|T=0] *)
Lemma consistency_control_mean :
  consistency po T Y_obs ->
  (* E[Y_obs | T=0] = E[Y(0) | T=0] *)
  True. (* Placeholder *)
Proof. done. Qed.

(**
  The NAIVE COMPARISON:

  E[Y_obs | T=1] - E[Y_obs | T=0]

  This is NOT generally equal to ATE!

  By consistency:
  = E[Y(1) | T=1] - E[Y(0) | T=0]

  But ATE = E[Y(1)] - E[Y(0)]

  The difference is due to SELECTION BIAS:
  - Those who select into treatment may have different potential outcomes
  - E[Y(1) | T=1] ≠ E[Y(1)] in general (treated differ from population)
  - E[Y(0) | T=0] ≠ E[Y(0)] in general (controls differ from population)
*)

Definition naive_comparison : R :=
  (* E[Y_obs | T=1] - E[Y_obs | T=0] *)
  0. (* Placeholder - requires conditional expectations *)

(** Selection bias decomposes the naive comparison *)
Lemma selection_bias_decomposition :
  consistency po T Y_obs ->
  (* naive_comparison = ATE + selection_bias *)
  (* where selection_bias captures systematic differences between groups *)
  True.
Proof. done. Qed.

End Identification.

(* ========================================================================== *)
(*  Section 7: Summary for Beginners                                          *)
(* ========================================================================== *)

(**
  SUMMARY: THE POTENTIAL OUTCOMES FRAMEWORK

  1. FOR EACH UNIT, THERE ARE TWO POTENTIAL OUTCOMES:
     - Y(1): what would happen under treatment
     - Y(0): what would happen under control
     Both exist conceptually, but only one is ever observed.

  2. THE FUNDAMENTAL PROBLEM:
     We can never observe both Y(1) and Y(0) for the same unit.
     This makes individual causal effects (ITEs) unidentifiable.

  3. CAUSAL ESTIMANDS (what we want to know):
     - ATE = E[Y(1) - Y(0)]: average effect in population
     - ATT = E[Y(1) - Y(0) | T=1]: average effect on treated
     - ATC = E[Y(1) - Y(0) | T=0]: average effect on controls

  4. CONSISTENCY ASSUMPTION:
     The observed outcome equals the potential outcome for the
     treatment actually received: Y^obs = Y(T).

  5. IDENTIFICATION:
     To estimate ATE from observed data, we need additional assumptions:
     - Unconfoundedness: (Y(0), Y(1)) ⊥ T | X
     - Positivity: 0 < P(T=1|X) < 1 for all X
     These are formalized in CausalAssumptions.v.

  6. THE PROPENSITY SCORE (next files):
     The propensity score e(X) = P(T=1|X) plays a key role.
     Rosenbaum-Rubin showed: conditioning on e(X) suffices
     to remove confounding if unconfoundedness holds given X.
*)

(* ========================================================================== *)
(*  Exports                                                                   *)
(* ========================================================================== *)

#[global] Hint Unfold ATE ITE consistency : causal.
