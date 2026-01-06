(* ========================================================================== *)
(*                              Axioms.v                                      *)
(*                                                                            *)
(*  Classical axioms and foundations for causal inference formalization       *)
(*                                                                            *)
(*  This file centralizes the classical axioms needed for probability theory  *)
(*  and causal inference. We use MathComp-Analysis which already provides     *)
(*  these axioms consistently.                                                *)
(*                                                                            *)
(*  For beginners: Coq is based on constructive logic by default. For         *)
(*  probability theory, we need classical axioms like excluded middle         *)
(*  (P \/ ~P for any proposition P). These are standard in mathematics        *)
(*  and are provided by MathComp-Analysis.                                    *)
(* ========================================================================== *)

From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrnum.
From mathcomp Require Import mathcomp_extra boolp classical_sets.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ========================================================================== *)
(*  Section 1: Classical Logic Axioms                                         *)
(*                                                                            *)
(*  MathComp-Analysis provides these axioms in classical_sets.v:              *)
(*  - Excluded middle: forall P, P \/ ~P                                      *)
(*  - Propositional extensionality: (P <-> Q) -> P = Q                        *)
(*  - Functional extensionality: (forall x, f x = g x) -> f = g               *)
(*                                                                            *)
(*  These are consistent with Coq's type theory and widely used in            *)
(*  formalizations of analysis and probability.                               *)
(* ========================================================================== *)

Section ClassicalLogic.

(** Excluded middle is available as [classic] from classical_sets.v *)
(** For any proposition P, either P holds or its negation ~P holds. *)

Lemma excluded_middle : forall P : Prop, P \/ ~ P.
Proof. exact: EM. Qed.

(** Proof by contradiction: to prove P, assume ~P and derive False *)
Lemma proof_by_contradiction : forall P : Prop, (~ P -> False) -> P.
Proof.
  move=> P Hnnp.
  case: (EM P) => [Hp | Hnp].
  - exact Hp.
  - exfalso. apply Hnnp. exact Hnp.
Qed.

(** Double negation elimination *)
Lemma double_negation : forall P : Prop, ~ ~ P -> P.
Proof.
  move=> P Hnnp.
  apply: proof_by_contradiction.
  exact: Hnnp.
Qed.

(** De Morgan's laws for classical logic *)
Lemma not_and_or : forall P Q : Prop, ~ (P /\ Q) <-> (~ P \/ ~ Q).
Proof.
  move=> P Q; split.
  - move=> Hna.
    case: (EM P) => [Hp | Hnp]; [right | by left].
    move=> Hq.
    apply: Hna.
    by split.
  - move=> [Hnp | Hnq] [Hp Hq]; [exact: Hnp | exact: Hnq].
Qed.

Lemma not_or_and : forall P Q : Prop, ~ (P \/ Q) <-> (~ P /\ ~ Q).
Proof.
  move=> P Q; split.
  - move=> Hno; split => H; apply: Hno; [by left | by right].
  - move=> [Hnp Hnq] [Hp | Hq]; [exact: Hnp | exact: Hnq].
Qed.

End ClassicalLogic.

(* ========================================================================== *)
(*  Section 2: Extensionality Principles                                      *)
(*                                                                            *)
(*  Extensionality allows us to prove equality of propositions, functions,    *)
(*  and sets by their behavior rather than their definitions.                 *)
(* ========================================================================== *)

Section Extensionality.

(** Propositional extensionality: equivalent propositions are equal *)
(** This is crucial for set equality: {x | P x} = {x | Q x} when P <-> Q *)
Lemma prop_extensionality : forall P Q : Prop, (P <-> Q) -> P = Q.
Proof. exact: propext. Qed.

(** Functional extensionality for dependent functions *)
(** Two functions are equal if they agree on all inputs *)
Lemma fun_extensionality : forall (A : Type) (B : A -> Type)
  (f g : forall x : A, B x),
  (forall x, f x = g x) -> f = g.
Proof. exact: functional_extensionality_dep. Qed.

(** Non-dependent version *)
Lemma fun_ext : forall (A B : Type) (f g : A -> B),
  (forall x, f x = g x) -> f = g.
Proof. move=> A B f g H. exact: fun_extensionality. Qed.

End Extensionality.

(* ========================================================================== *)
(*  Section 3: Decidability Helpers                                           *)
(*                                                                            *)
(*  Classical logic gives us decidability for all propositions, which is      *)
(*  useful for case analysis in proofs.                                       *)
(* ========================================================================== *)

Section Decidability.

(** Any proposition is decidable classically *)
(** pselect from MathComp-Analysis provides {P} + {~P} *)
Definition classically_decidable (P : Prop) : {P} + {~ P} := pselect P.

(** Boolean reflection for classical propositions *)
(** This connects classical propositions to boolean computations *)
Definition prop_to_bool (P : Prop) : bool :=
  if classically_decidable P then true else false.

Lemma prop_to_boolP (P : Prop) : reflect P (prop_to_bool P).
Proof.
  rewrite /prop_to_bool.
  case: (classically_decidable P) => H.
  - by constructor.
  - by constructor.
Qed.

End Decidability.

(* ========================================================================== *)
(*  Section 4: Set Theory Foundations                                         *)
(*                                                                            *)
(*  We use MathComp-Analysis's set theory, which provides:                    *)
(*  - Sets as predicates: set T = T -> Prop                                   *)
(*  - Standard set operations with nice notation                              *)
(*  - Measurable sets for probability theory                                  *)
(* ========================================================================== *)

Section SetTheory.

Variable (T : Type).

(** Sets are predicates in MathComp-Analysis *)
(** A set A : set T is a function T -> Prop *)

(** The empty set *)
Check (@set0 T) : set T.

(** The full set (all elements) *)
Check (@setT T) : set T.

(** Set membership: x \in A *)
(** Note: This uses the \in notation from ssrbool *)

(** Set comprehension: [set x | P x] *)
(** Creates the set of all x satisfying predicate P *)

(** Key operations available:
    - A `|` B : union
    - A `&` B : intersection
    - ~` A    : complement
    - A `\` B : difference
    - A `<=` B : subset
*)

End SetTheory.

(* ========================================================================== *)
(*  Section 5: Why These Axioms for Causal Inference?                         *)
(*                                                                            *)
(*  For beginners: Here's why we need classical logic for causal inference.   *)
(* ========================================================================== *)

(**
  1. EXCLUDED MIDDLE is needed for:
     - Case analysis on whether a unit is treated or not
     - Reasoning about whether events have positive probability
     - Proving inequalities by contradiction

  2. PROPOSITIONAL EXTENSIONALITY is needed for:
     - Proving equality of events (sets of outcomes)
     - Showing {x | P x} = {x | Q x} when P and Q are equivalent
     - Set-theoretic reasoning about probability spaces

  3. FUNCTIONAL EXTENSIONALITY is needed for:
     - Proving equality of random variables
     - Showing two distributions are equal by their density/mass functions
     - Equality of conditional expectations

  4. CHOICE AXIOMS (provided by MathComp-Analysis) are needed for:
     - Existence of conditional expectations
     - Existence of regular conditional distributions
     - Selecting representatives from equivalence classes

  These axioms are standard in mathematical practice and are consistent
  with Coq's type theory. MathComp-Analysis has carefully integrated them
  for use in measure theory and probability.
*)

(* ========================================================================== *)
(*  Section 6: Tactics and Automation                                         *)
(*                                                                            *)
(*  Helpful tactics for classical reasoning                                   *)
(* ========================================================================== *)

(** Use classical reasoning: by_contra introduces ~P as hypothesis *)
Ltac by_contra :=
  match goal with
  | |- ?P => apply proof_by_contradiction; intro
  end.

(** Classical case split: handles P \/ ~P *)
Ltac classical_case P :=
  case: (EM P).

(** Example of classical reasoning *)
Lemma example_classical : forall P Q : Prop,
  ((P -> Q) -> P) -> P.
Proof.
  move=> P Q H.
  classical_case P => [Hp | Hnp].
  - exact: Hp.
  - apply: H => Hp.
    by exfalso; apply: Hnp.
Qed.

(* ========================================================================== *)
(*  Exports                                                                   *)
(* ========================================================================== *)

(** We export the key lemmas for use in other files *)

(** We export key lemmas - note that universal quantifier lemmas
    require Hint Extern for proper hint registration *)
