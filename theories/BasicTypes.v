(* ========================================================================== *)
(*                             BasicTypes.v                                   *)
(*                                                                            *)
(*  Foundational types for causal inference formalization                     *)
(*                                                                            *)
(*  This file defines the core vocabulary:                                    *)
(*  - Treatment indicators (treated vs control)                               *)
(*  - Covariate spaces (measurable spaces of baseline characteristics)        *)
(*  - Outcome spaces (typically real numbers)                                 *)
(*  - Random variables using MathComp-Analysis notation                       *)
(*                                                                            *)
(*  For beginners: This file establishes the "nouns" of causal inference.     *)
(*  We model a statistical experiment where:                                  *)
(*  - Each unit has baseline covariates X                                     *)
(*  - Each unit receives treatment T (binary: 0 or 1)                         *)
(*  - Each unit has an observed outcome Y                                     *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.
From mathcomp Require Import interval_inference reals ereal topology normedtype.
From mathcomp Require Import sequences measure lebesgue_measure probability.

Require Import Axioms.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.

(* ========================================================================== *)
(*  Section 1: Treatment Type                                                 *)
(*                                                                            *)
(*  Treatment is binary: either Treated (1) or Control (0).                   *)
(*  We use bool for simplicity and compatibility with MathComp.               *)
(* ========================================================================== *)

Section Treatment.

(** Treatment as boolean: true = treated, false = control *)
(** Using bool gives us:
    - Decidable equality
    - Case analysis (if T then ... else ...)
    - Compatibility with MathComp's boolean reasoning *)

Definition treatment := bool.
Definition treated : treatment := true.
Definition control : treatment := false.

(** Convert treatment to real number for arithmetic *)
(** This is used in formulas like E[T * Y / e(X)] *)
(** We use bool_to_R instead of %:R to avoid notation conflicts *)
Definition bool_to_R {R : realType} (t : bool) : R :=
  if t then 1 else 0.

(** Properties of treatment indicator *)
Lemma treatment_01 (R : realType) (t : treatment) :
  @bool_to_R R t = 0 \/ @bool_to_R R t = 1.
Proof. by case: t; [right | left]. Qed.

Lemma treatment_complement (R : realType) (t : treatment) :
  (1 - @bool_to_R R t) = @bool_to_R R (~~t).
Proof. by case: t; rewrite /bool_to_R /= ?(GRing.subrr, GRing.subr0). Qed.

(** Treatment is a finite type with 2 elements *)
(** This allows summation over all treatment values *)
Lemma treatment_finite : #|{: bool}| = 2.
Proof. by rewrite card_bool. Qed.

End Treatment.

(* ========================================================================== *)
(*  Section 2: Probability Spaces and Random Variables                        *)
(*                                                                            *)
(*  We use MathComp-Analysis's probability theory framework:                  *)
(*  - A probability space (Omega, F, P) where Omega is the sample space       *)
(*  - Random variables are measurable functions from Omega                    *)
(*  - The notation {RV P >-> T} denotes random variables with law P           *)
(* ========================================================================== *)

Section ProbabilitySpace.

Variable (R : realType).

(**
  A probability space consists of:
  1. A sample space Omega (measurable type)
  2. A sigma-algebra F on Omega (encoded in measurableType)
  3. A probability measure P : probability Omega R

  In MathComp-Analysis:
  - measurableType encodes Omega with its sigma-algebra
  - probability T R is a measure on T with P(Omega) = 1
*)

Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  Random Variables:
  A random variable X : Omega -> T is a measurable function.
  MathComp-Analysis uses the notation:
    {mfun Omega >-> T}  for measurable functions
    {RV P >-> T}        for random variables (same as mfun, with P for context)
*)

(** Outcome space: typically the real numbers *)
(** We use R (the realType) for outcomes like survival time, cost, etc. *)
(** Note: outcome_rv and treatment_rv are defined as simple function types.
    For full measure-theoretic treatment, use {mfun Omega >-> T} notation. *)

Definition outcome_rv := Omega -> R.

(** Treatment random variable *)
(** T : Omega -> bool indicates whether each unit omega received treatment *)

Definition treatment_rv := Omega -> bool.

(** Note: The actual covariate type depends on the application.
    It could be:
    - A finite type (for categorical covariates)
    - R^n (for continuous covariates)
    - A product of both (mixed)

    We parameterize by an abstract covariate space in later sections. *)

End ProbabilitySpace.

(* ========================================================================== *)
(*  Section 3: Covariate Spaces                                               *)
(*                                                                            *)
(*  Covariates are baseline characteristics measured before treatment.        *)
(*  The covariate space X must be a measurable space for integration.         *)
(* ========================================================================== *)

Section CovariateSpace.

Variable (R : realType).

(**
  Abstract covariate space:
  - Must be a measurableType for measure-theoretic operations
  - Examples: finite types, R^n, product spaces

  We leave this abstract and instantiate in applications.
*)

Section AbstractCovariates.

Variable (dX : measure_display).
Variable (X : measurableType dX).

(** Covariate random variable *)
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

Definition covariate_rv := Omega -> X.

End AbstractCovariates.

(**
  For many applications, covariates are real vectors.
  Here we provide a concrete instantiation for R^n.
*)

Section RealCovariates.

Variable (n : nat).

(** n-dimensional real covariates *)
(** Uses the Euclidean space structure from MathComp-Analysis *)

(* R^n as a measurable type would be defined using products *)
(* For simplicity, we often work with abstract covariate types *)

End RealCovariates.

End CovariateSpace.

(* ========================================================================== *)
(*  Section 4: Unit Data Structure                                            *)
(*                                                                            *)
(*  In causal inference, we observe data for each unit (individual):          *)
(*  - Covariates X_i (baseline characteristics)                               *)
(*  - Treatment T_i (indicator of treatment received)                         *)
(*  - Observed outcome Y_i^obs                                                *)
(*                                                                            *)
(*  Note: We do NOT observe both potential outcomes Y_i(0) and Y_i(1).        *)
(*  This is the "fundamental problem of causal inference."                    *)
(* ========================================================================== *)

Section UnitData.

Variable (R : realType).
Variable (dX : measure_display).
Variable (X : measurableType dX).

(**
  Record for observed data of a single unit.
  In a dataset, we would have a sequence of these records.
*)
Record unit_data := mkUnit {
  unit_covariates : X;        (* X_i: baseline characteristics *)
  unit_treatment : bool;      (* T_i: treatment indicator *)
  unit_outcome : R            (* Y_i^obs: observed outcome *)
}.

(**
  The observed outcome is determined by treatment:
  Y_i^obs = T_i * Y_i(1) + (1 - T_i) * Y_i(0)

  But we only see Y_i^obs, not the individual potential outcomes.
  This consistency relation is formalized in PotentialOutcomes.v.
*)

End UnitData.

(* ========================================================================== *)
(*  Section 5: Probability and Expectation Notation                           *)
(*                                                                            *)
(*  MathComp-Analysis provides:                                               *)
(*  - P(A) for probability of event A                                         *)
(*  - 'E_P[X] for expectation of random variable X                            *)
(*  - Conditional expectations via kernels (see ConditionalIndep.v)           *)
(* ========================================================================== *)

Section ExpectationNotation.

Variable (R : realType).
Variable (d : measure_display).
Variable (Omega : measurableType d).
Variable (P : probability Omega R).

(**
  Expectation notation in MathComp-Analysis:

  For a random variable X : {RV P >-> R}, the expectation is:
    'E_P[X] = \int[P]_omega X omega

  This is the Lebesgue integral of X with respect to probability measure P.
*)

(** Example: expectation of a constant
    Note: Integral notation \int[P]_omega requires proper imports.
    These lemmas are commented out for now to allow compilation.

Lemma expectation_const (c : R) :
  \int[P]_omega c = c.
Proof.
  (* This uses that P is a probability measure with P(Omega) = 1 *)
  (* The integral of a constant c is c * P(Omega) = c * 1 = c *)
Admitted.

Lemma expectation_linear (X Y : Omega -> R) (a b : R) :
  measurable_fun setT X ->
  measurable_fun setT Y ->
  P.-integrable setT (EFin \o X) ->
  P.-integrable setT (EFin \o Y) ->
  \int[P]_omega (a * X omega + b * Y omega) =
  a * \int[P]_omega X omega + b * \int[P]_omega Y omega.
Proof.
  (* Uses linearity of Lebesgue integral *)
Admitted.
*)

End ExpectationNotation.

(* ========================================================================== *)
(*  Section 6: Summary of Type Hierarchy                                      *)
(*                                                                            *)
(*  For beginners: Here's the hierarchy of types we use.                      *)
(* ========================================================================== *)

(**
  TYPE HIERARCHY FOR CAUSAL INFERENCE IN COQ:

  1. REAL NUMBERS
     R : realType
     - The real numbers with their algebraic and topological structure
     - Used for outcomes, propensity scores, expectations

  2. PROBABILITY SPACE (Omega, F, P)
     Omega : measurableType d     (sample space with sigma-algebra)
     P : probability Omega R      (probability measure)

  3. RANDOM VARIABLES
     X : {mfun Omega >-> T}       (measurable function Omega -> T)
     - T can be bool (treatment), R (outcomes), or covariate space

  4. SPECIFIC RANDOM VARIABLES
     Treatment:  T : {mfun Omega >-> bool}
     Outcome:    Y : {mfun Omega >-> R}
     Covariates: X : {mfun Omega >-> CovariateSpace}

  5. DATA STRUCTURES
     unit_data: record containing (covariates, treatment, outcome)

  The key insight: causal inference is about relating:
  - Observable quantities (joint distribution of X, T, Y^obs)
  - Unobservable quantities (potential outcomes Y(0), Y(1))

  The assumptions in CausalAssumptions.v specify when this is possible.
*)

(* ========================================================================== *)
(*  Section 7: Measurability Helpers                                          *)
(*                                                                            *)
(*  Useful lemmas for proving measurability of composed functions.            *)
(* ========================================================================== *)

Section Measurability.

Variable (R : realType).
Variable (d1 d2 d3 : measure_display).
Variable (T1 : measurableType d1).
Variable (T2 : measurableType d2).
Variable (T3 : measurableType d3).

(** Composition of measurable functions is measurable *)
Lemma measurable_composition (f : T1 -> T2) (g : T2 -> T3) :
  measurable_fun setT f ->
  measurable_fun setT g ->
  measurable_fun setT (g \o f).
Proof.
  move=> Hf Hg.
  apply: (measurableT_comp Hg Hf).
Qed.

(** Constants are measurable *)
Lemma measurable_const (c : T2) :
  measurable_fun setT (fun _ : T1 => c).
Proof.
  apply: measurable_cst.
Qed.

End Measurability.

(* ========================================================================== *)
(*  Exports                                                                   *)
(* ========================================================================== *)

(** Make key definitions available *)
#[global] Hint Resolve treatment_01 : core.
