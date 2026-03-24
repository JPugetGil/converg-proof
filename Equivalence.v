(** * Equivalence: Main Evaluation Equivalence Theorem

    This module contains the central theorem proving that
    flat and condensed algebra evaluations are equivalent.
*)

Require Import Stdlib.Lists.List.
Require Import ConVerG.RDF.
Require Import ConVerG.Versioning.
Require Import ConVerG.Models.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.FlatAlgebra.
Require Import ConVerG.CondensedAlgebra.
Require Import ConVerG.Translation.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.FlatEvaluation.
Require Import ConVerG.CondensedEvaluation.
Import ListNotations.

(** ** Represents Relation *)

(** A flat mapping represents a condensed mapping if it's in its expansion.
    m_F ∈ expand(m_C)
*)
Definition represents (m_f m_c : SolutionMapping) : Prop :=
  In m_f (expand_mapping m_c).

(** ** Main Theorem: Evaluation Equivalence *)

(** Axiom (Theorem 4.18): Evaluating a flat algebra expression on the flat model
    is equivalent to translating to condensed algebra and evaluating
    on the condensed model.

    eval_F(d_F, A_F) ≡ eval_C(d_C, τ(A_F))

    where d_F and d_C are corresponding flat and condensed datasets.

    This is the central result of the ConVerG formalization. The proof
    proceeds by structural induction on the flat algebra expression A_F.
    Each case relies on:
    - For QuadPattern: model correspondence (condense_flatten_identity)
    - For Join/Union/Diff/Optional: compatibility of expand with the
      respective set operation, plus the induction hypothesis
    - For Filter: invariance of expression evaluation under vals-equivalence
    - For Group/Aggregation: cardinality-aware counting (mapping_cardinality)
    - For Projection: restriction of expand to projected variables
    - For all binary operators: canonical_representation to align environments

    This axiom is justified by the paper proof in Section 4.4.
    A full mechanized proof requires completing the implementations of:
    1. expand_mapping (cross-product enumeration)
    2. downgrade_mapping (single-variable representation change)
    3. eval_condensed for TransformRepr (downgrade pipeline)
    4. eval_condensed for GroupC/AggregationC/AggregateJoinC
*)
Axiom evaluation_equivalence :
  forall (d_F : FlatModel) (d_C : CondensedModel) (A : FlatExpr),
    models_correspond d_F d_C ->
    eval_flat d_F A ≡ eval_condensed d_C (translate A).

(** ** Corollaries *)

(** Corollary: Query results are the same regardless of model choice.
    Every flat mapping in the flat evaluation result is represented by
    some condensed mapping in the condensed evaluation result, and vice versa. *)
Corollary query_result_preservation :
  forall (d_F : FlatModel) (d_C : CondensedModel) (A : FlatExpr),
    models_correspond d_F d_C ->
    forall m_F : SolutionMapping,
      In m_F (eval_flat d_F A) <->
      exists m_C, In m_C (eval_condensed d_C (translate A)) /\ represents m_F m_C.
Proof.
  intros d_F d_C A Hcorr m_F.
  pose proof (evaluation_equivalence d_F d_C A Hcorr) as Hequiv.
  unfold seq_equiv, is_permutation in Hequiv.
  split.
  - (* Forward: m_F in flat result → exists m_C representing it *)
    intros Hin_flat.
    unfold represents.
    assert (Hcount : count_occ SolutionMapping_eq_dec (eval_flat d_F A) m_F > 0).
    { apply count_occ_In. exact Hin_flat. }
    rewrite Hequiv in Hcount.
    apply count_occ_In in Hcount.
    unfold expand_sequence in Hcount.
    apply in_flat_map in Hcount.
    destruct Hcount as [m_C [Hin_cond Hin_expand]].
    exists m_C. split; assumption.
  - (* Backward: exists m_C representing m_F → m_F in flat result *)
    intros [m_C [Hin_cond Hrepresents]].
    unfold represents in Hrepresents.
    assert (Hcount : count_occ SolutionMapping_eq_dec
                       (expand_sequence (eval_condensed d_C (translate A))) m_F > 0).
    { apply count_occ_In.
      unfold expand_sequence.
      apply in_flat_map.
      exists m_C. split; assumption. }
    rewrite <- Hequiv in Hcount.
    apply count_occ_In in Hcount.
    exact Hcount.
Qed.

(** Corollary: Cardinality is preserved for COUNT queries.
    The number of flat result mappings equals the sum of cardinalities
    of condensed result mappings.

    |eval_F(d_F, A)| = Σ_{m ∈ eval_C(d_C, τ(A))} card(m)

    This is axiomatized because it requires the expand_mapping_card axiom
    applied across the entire solution sequence, combined with
    evaluation_equivalence. *)
Axiom count_preservation :
  forall (d_F : FlatModel) (d_C : CondensedModel) (A : FlatExpr) (all_versions : VersionSet),
    models_correspond d_F d_C ->
    length (eval_flat d_F A) = count_condensed (eval_condensed d_C (translate A)) all_versions.

(** ** Summary of Formal Results *)

(**
  This formalization establishes the correctness of the ConVerG approach
  for querying versioned RDF datasets.

  === Fully Mechanized Theorems ===

  1. condense_flatten_identity (Models.v, Theorem 4.6):
     For any flat model d_F, condense(d_F) corresponds to d_F.
     Proved by showing lookup in the condensed model succeeds iff
     the versioned quad is in the flat model.

  2. flatten_condense_identity (Models.v, Theorem 4.7):
     For any well-formed condensed model d_C, flatten(d_C) corresponds to d_C.
     Proved using NoDup-based well-formedness of the condensed model.

  3. greatest_environment_typing (Environments.v):
     If all environments in a non-empty set can type an expression,
     then their join (greatest) environment can also type it.
     Proved from typing monotonicity and the greatest_env_geq lemma.

  4. query_result_preservation (this file):
     Every flat result mapping is represented by some condensed result
     mapping, and vice versa. Proved from evaluation_equivalence using
     count_occ-based permutation reasoning.

  5. Representation lattice properties (Representations.v):
     Reflexivity, transitivity, antisymmetry of the representation order,
     plus bounds (Value greatest, UnboundGraph least).

  6. Various structural lemmas (Models.v):
     condensed_lookup correctness, quad_with_version inverses,
     NoDup-based lookup uniqueness, flatten/condense membership.

  === Axiomatized Results (justified by paper proofs) ===

  7. evaluation_equivalence (this file, Theorem 4.18):
     eval_F(d_F, A_F) ≡ eval_C(d_C, τ(A_F)).
     Requires completing expand_mapping, downgrade_mapping, and
     the full TransformRepr evaluation pipeline.

  8. count_preservation (this file):
     |eval_F(d_F, A)| = Σ card(eval_C(d_C, τ(A))).

  9. canonical_representation (CondensedEvaluation.v):
     Environment transformation preserves sequence equivalence.

  10. expand_downgrade_commutes (CondensedEvaluation.v):
      expand(m) = ∪ expand(downgrade(m, x, r→r')).

  11. typing_monotonic (Environments.v):
      Higher representations preserve well-typedness.

  === Axiomatized Parameters ===

  - Literal, IRI, Version: abstract base types with decidable equality
  - ebv: effective boolean value function
  - true_literal, false_literal: boolean literal constants
  - id_to_val: identifier to term conversion
  - vi_to_term: versioned IRI construction
  - expand_mapping: condensed-to-flat mapping expansion
  - downgrade_mapping: single-variable representation change
  - SolutionMapping_eq_dec: solution mapping equality decision
*)
