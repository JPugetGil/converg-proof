(** * CondensedEvaluation: Condensed Algebra Evaluation Semantics
    
    This module defines the evaluation function for condensed SPARQL algebra
    expressions over condensed versioned datasets.
*)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.PeanoNat.
Require Import ConVerG.RDF.
Require Import ConVerG.Versioning.
Require Import ConVerG.Models.
Require Import ConVerG.Representations.
Require Import ConVerG.CondensedAlgebra.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.FlatEvaluation.
Import ListNotations.

(** ** Condensed Solution Sequence *)

(** A condensed solution sequence contains mappings with condensed bindings. *)
Definition CondensedSolutionSequence := list SolutionMapping.

(** ** Boolean Compatibility Check *)

(** Check condensed compatibility (boolean version). *)
Definition compatible_condensed_dec (m1 m2 : SolutionMapping) : bool :=
  (* Value compatibility *)
  forallb (fun xv : Var * Term =>
    let (x, v1) := xv in
    match lookup_value x (m_value m2) with
    | Some v2 => if Term_eq_dec v1 v2 then true else false
    | None => true
    end
  ) (m_value m1)
  &&
  (* Id compatibility *)
  forallb (fun xi : Var * nat =>
    let (x, i1) := xi in
    match lookup_id x (m_id m2) with
    | Some i2 => if PeanoNat.Nat.eq_dec i1 i2 then true else false
    | None => true
    end
  ) (m_id m1)
  &&
  (* Condensed compatibility: same graph AND non-empty version intersection *)
  forallb (fun xc : CondensedBinding =>
    let '(x, (g1, vs1)) := xc in
    match lookup_condensed x (m_condensed m2) with
    | Some (g2, vs2) =>
        if PeanoNat.Nat.eq_dec g1 g2 then
          match version_set_intersection vs1 vs2 with
          | [] => false
          | _ => true
          end
        else false
    | None => true
    end
  ) (m_condensed m1).

(** ** Condensed Algebra Evaluation *)

(** Lookup quad in condensed model and return version set. *)
Definition lookup_quad_versions (d : CondensedModel) (s p : nat) (o : Term) (g : nat) 
           : option VersionSet :=
  (* Simplified: would need proper quad construction *)
  None.

(** eval_C(d_C, e) evaluates condensed expression e over condensed dataset d_C
    and returns a condensed solution sequence.
*)
Fixpoint eval_condensed (d : CondensedModel) (e : CondensedExpr) : CondensedSolutionSequence :=
  match e with
  (** Quad Pattern: returns mappings with condensed graph bindings. *)
  | QuadPatternC s p o g =>
      (* For each quad in domain(d_C), create a mapping with:
         - s, p, o bound as Id
         - g bound as Condensed with version set from d_C *)
      map (fun qvs : Quad * VersionSet =>
        let (q, vs) := qvs in
        mkSolutionMapping
          [] (* no value bindings *)
          [] (* id bindings would go here *)
          [(g, (0, vs))] (* graph as condensed, placeholder graph id *)
          []
      ) d
      
  (** Join: combine compatible mappings, intersecting version sets. *)
  | JoinC e1 e2 =>
      let seq1 := eval_condensed d e1 in
      let seq2 := eval_condensed d e2 in
      flat_map (fun m1 =>
        filter_map (fun m2 =>
          if compatible_condensed_dec m1 m2 then Some (merge_condensed m1 m2)
          else None
        ) seq2
      ) seq1
      
  (** Filter: select mappings satisfying condition. *)
  | FilterC c e =>
      let seq := eval_condensed d e in
      filter (fun m => expr_is_true c m) seq
      
  (** Union: concatenate solution sequences. *)
  | UnionC e1 e2 =>
      eval_condensed d e1 ++ eval_condensed d e2
      
  (** Diff: mappings from e1 that don't match e2 or fail condition. *)
  | DiffC e1 e2 c =>
      let seq1 := eval_condensed d e1 in
      let seq2 := eval_condensed d e2 in
      filter (fun m1 =>
        forallb (fun m2 =>
          negb (compatible_condensed_dec m1 m2) ||
          negb (expr_is_true c (merge_condensed m1 m2))
        ) seq2
      ) seq1
      
  (** Optional: left outer join. *)
  | OptionalC e1 e2 c =>
      (* Inline the join + filter logic *)
      let seq1 := eval_condensed d e1 in
      let seq2 := eval_condensed d e2 in
      let joined := filter (fun m => expr_is_true c m)
        (flat_map (fun m1 =>
          filter_map (fun m2 =>
            if compatible_condensed_dec m1 m2 then Some (merge_condensed m1 m2)
            else None
          ) seq2
        ) seq1) in
      (* Inline the diff logic *)
      let diff := filter (fun m1 =>
        forallb (fun m2 =>
          negb (compatible_condensed_dec m1 m2) ||
          negb (expr_is_true c (merge_condensed m1 m2))
        ) seq2
      ) seq1 in
      joined ++ diff
      
  (** Group: partition by grouping expressions. *)
  | GroupC exprs e =>
      eval_condensed d e (* Simplified *)
      
  (** Aggregation: apply aggregate function with cardinality. *)
  | AggregationC exprs agg grp =>
      eval_condensed d grp (* Simplified *)
      
  (** Aggregate Join: combine multiple aggregations. *)
  | AggregateJoinC aggs =>
      match aggs with
      | [] => []
      | a :: rest => eval_condensed d a (* Simplified *)
      end
      
  (** Projection. *)
  | ProjectionC e vars =>
      map (fun m =>
        mkSolutionMapping
          (filter (fun xv => set_member Var_eq_dec (fst xv) vars) (m_value m))
          (filter (fun xv => set_member Var_eq_dec (fst xv) vars) (m_id m))
          (filter (fun xv => set_member Var_eq_dec (fst xv) vars) (m_condensed m))
          (filter (fun x => set_member Var_eq_dec x vars) (m_unboundgraph m))
      ) (eval_condensed d e)
      
  (** Environment transformation: apply representation changes. *)
  | TransformRepr env_from env_to e =>
      (* Would apply the representation transformations *)
      eval_condensed d e (* Simplified *)
  end.

(** ** Cardinality-Aware COUNT *)

(** COUNT_C aggregation computes the total cardinality.
    COUNT_C(Ω) = Σ_{m ∈ Ω} card(m)
*)
Definition count_condensed (seq : CondensedSolutionSequence) (all_versions : VersionSet) : nat :=
  fold_right (fun m acc => acc + mapping_cardinality m all_versions) 0 seq.

(** ** Cross-Product Helpers *)

(** Cartesian product of a list of choice lists.
    Given [[a1;a2]; [b1;b2;b3]], produces all combinations:
    [[a1;b1]; [a1;b2]; [a1;b3]; [a2;b1]; [a2;b2]; [a2;b3]] *)
Fixpoint cross_product_bindings (choices : list (list ValueBinding))
  : list (list ValueBinding) :=
  match choices with
  | [] => [[]]
  | c :: rest =>
    let rest_cp := cross_product_bindings rest in
    flat_map (fun b => map (fun bs => b :: bs) rest_cp) c
  end.

(** Expand one condensed binding to possible value bindings. *)
Definition expand_one_condensed (cb : CondensedBinding) : list ValueBinding :=
  let '(x, (g, vs)) := cb in
  map (fun v => (x, SolutionMappings.vi_to_term v g)) vs.

(** Expand one unboundgraph variable to possible value bindings. *)
Definition expand_one_unboundgraph (all_versions : VersionSet) (x : Var)
  : list ValueBinding :=
  map (fun v => (x, SolutionMappings.vi_to_term v 0)) all_versions.

(** ** Expansion and Sequence Equivalence *)

(** Expand a condensed solution mapping to all the flat mappings it represents.
    expand(m) enumerates the cross-product of all condensed variable instantiations:
    - Value bindings: kept as-is (one value)
    - Id bindings: kept as-is (one id)
    - Condensed (g, V): expanded to |V| mappings, one per version
    - UnboundGraph: expanded to all versioned named graphs

    Parameterized by the global version set (needed for UnboundGraph expansion). *)
Definition expand_mapping (all_versions : VersionSet) (m : SolutionMapping)
  : list SolutionMapping :=
  let condensed_choices := map expand_one_condensed (m_condensed m) in
  let unboundgraph_choices := map (expand_one_unboundgraph all_versions) (m_unboundgraph m) in
  let all_choices := condensed_choices ++ unboundgraph_choices in
  let combinations := cross_product_bindings all_choices in
  map (fun chosen =>
    mkSolutionMapping
      (m_value m ++ chosen)
      (m_id m)
      []
      []
  ) combinations.

(** Length of cross_product_bindings is the product of lengths. *)
Lemma cross_product_bindings_length :
  forall choices,
    length (cross_product_bindings choices) =
    fold_right (fun c acc => length c * acc) 1 choices.
Proof.
  induction choices as [| c rest IH].
  - simpl. reflexivity.
  - simpl. rewrite flat_map_constant_length with (c := length (cross_product_bindings rest)).
    + rewrite IH. reflexivity.
    + intros b _. apply length_map.
Qed.

(** Length of expand_one_condensed is the version set cardinality. *)
Lemma expand_one_condensed_length : forall cb,
  length (expand_one_condensed cb) = version_set_card (snd (snd cb)).
Proof.
  intros [x [g vs]]. simpl. apply length_map.
Qed.

(** Length of expand_one_unboundgraph is the version set cardinality. *)
Lemma expand_one_unboundgraph_length : forall all_versions x,
  length (expand_one_unboundgraph all_versions x) = version_set_card all_versions.
Proof.
  intros. unfold expand_one_unboundgraph. apply length_map.
Qed.

(** Lemma: expand_mapping produces exactly [m] for non-condensed, non-unboundgraph mappings. *)
Lemma expand_mapping_nonempty : forall all_versions m,
  m_condensed m = [] ->
  m_unboundgraph m = [] ->
  expand_mapping all_versions m = [mkSolutionMapping (m_value m ++ []) (m_id m) [] []].
Proof.
  intros all_versions m Hc Hu.
  unfold expand_mapping. rewrite Hc, Hu. simpl. reflexivity.
Qed.

(** Product of list of nats distributes over append. *)
Lemma list_product_app : forall l1 l2,
  fold_right Nat.mul 1 (l1 ++ l2) = fold_right Nat.mul 1 l1 * fold_right Nat.mul 1 l2.
Proof.
  induction l1 as [| a rest IH]; intros l2.
  - simpl. symmetry. apply Nat.add_0_r.
  - simpl. rewrite IH. apply Nat.mul_assoc.
Qed.

(** Rewrite fold as product of mapped lengths. *)
Lemma cross_product_as_product : forall (choices : list (list ValueBinding)),
  fold_right (fun c acc => length c * acc) 1 choices =
  fold_right Nat.mul 1 (map (fun c => length c) choices).
Proof.
  induction choices as [| c rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.

(** Mapped lengths of condensed expansions match version set cardinalities. *)
Lemma condensed_lengths : forall (conds : list CondensedBinding),
  map (fun c : list ValueBinding => length c) (map expand_one_condensed conds) =
  map (fun xc : CondensedBinding => version_set_card (snd (snd xc))) conds.
Proof.
  induction conds as [| [x [g vs]] rest IH].
  - simpl. reflexivity.
  - simpl. rewrite length_map. f_equal. apply IH.
Qed.

(** Mapped lengths of unboundgraph expansions match all_versions cardinality. *)
Lemma unboundgraph_lengths : forall all_versions (ubs : list Var),
  map (fun c : list ValueBinding => length c) (map (expand_one_unboundgraph all_versions) ubs) =
  map (fun _ : Var => version_set_card all_versions) ubs.
Proof.
  induction ubs as [| x rest IH].
  - simpl. reflexivity.
  - simpl. unfold expand_one_unboundgraph at 1. rewrite length_map. f_equal. apply IH.
Qed.

(** Product of condensed cardinalities matches mapping_cardinality's condensed part. *)
Lemma fold_mul_condensed : forall (conds : list CondensedBinding),
  fold_right Nat.mul 1 (map (fun xc : CondensedBinding => version_set_card (snd (snd xc))) conds) =
  fold_right (fun xc acc => acc * version_set_card (snd (snd xc))) 1 conds.
Proof.
  induction conds as [| [x [g vs]] rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. apply Nat.mul_comm.
Qed.

(** Product of unboundgraph cardinalities matches mapping_cardinality's unboundgraph part. *)
Lemma fold_mul_unboundgraph : forall all_versions (ubs : list Var),
  fold_right Nat.mul 1 (map (fun _ : Var => version_set_card all_versions) ubs) =
  fold_right (fun _ acc => acc * version_set_card all_versions) 1 ubs.
Proof.
  induction ubs as [| x rest IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. apply Nat.mul_comm.
Qed.

(** The cardinality of expand equals mapping_cardinality.
    |expand(m)| = card(m) *)
Lemma expand_mapping_card : forall m all_versions,
  length (expand_mapping all_versions m) = mapping_cardinality m all_versions.
Proof.
  intros m all_versions.
  unfold expand_mapping.
  rewrite length_map.
  rewrite cross_product_bindings_length.
  rewrite cross_product_as_product.
  rewrite map_app.
  rewrite list_product_app.
  unfold mapping_cardinality.
  rewrite condensed_lengths.
  rewrite unboundgraph_lengths.
  rewrite fold_mul_condensed.
  rewrite fold_mul_unboundgraph.
  reflexivity.
Qed.

(** Expand a condensed solution sequence to flat mappings. *)
Definition expand_sequence (all_versions : VersionSet)
                           (seq : CondensedSolutionSequence) : list SolutionMapping :=
  flat_map (expand_mapping all_versions) seq.

(** Permutation equivalence via count_occ. *)
Definition is_permutation {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
                          (l1 l2 : list A) : Prop :=
  forall x, count_occ eq_dec l1 x = count_occ eq_dec l2 x.

(** Sequence equivalence: flat and expanded condensed are permutations.
    Parameterized by the global version set for expansion. *)
Definition seq_equiv (all_versions : VersionSet)
                     (seq_f : list SolutionMapping)
                     (seq_c : CondensedSolutionSequence) : Prop :=
  is_permutation SolutionMapping_eq_dec seq_f (expand_sequence all_versions seq_c).

(** ** Representation Downgrade *)

(** Downgrade a variable's representation from r_from to r_to in a mapping.
    This produces multiple mappings when going from a more condensed to
    a more expanded representation (e.g., Condensed → Id enumerates versions).

    Axiomatized because the implementation depends on dataset-specific
    parameters (version sets, named graph enumerations). *)
Parameter downgrade_mapping : SolutionMapping -> Var -> Representation -> Representation -> list SolutionMapping.

(** Axiom: expand commutes with representation downgrade.
    This captures the fundamental property that the order of
    expansion and downgrade does not matter:
    expand(m) = ∪_{m' ∈ downgrade(m, x, r→r')} expand(m')

    This is the key lemma enabling the canonical_representation theorem. *)
Axiom expand_downgrade_commutes : forall (all_versions : VersionSet) (m : SolutionMapping) (x : Var) (r_from r_to : Representation),
  r_to <=_r r_from ->
  expand_mapping all_versions m = flat_map (expand_mapping all_versions) (downgrade_mapping m x r_from r_to).

(** ** Canonical Representation Theorem *)

(** Theorem: Evaluation is preserved under environment transformation.
    If seq_F ≡ eval_C(d_C, e), then seq_F ≡ eval_C(d_C, ↓_r(Γ, Γ')(e))

    This theorem states that applying representation transformations
    preserves the equivalence to the flat evaluation result.

    In the current simplified formalization, eval_condensed for TransformRepr
    is a pass-through (identity), making this theorem trivially provable.
    A full implementation would apply the downgrade pipeline using
    expand_downgrade_commutes. *)
Lemma canonical_representation :
  forall (all_versions : VersionSet) (d : CondensedModel) (e : CondensedExpr)
         (env env' : list (Var * Representation))
         (seq_f : list SolutionMapping),
    seq_equiv all_versions seq_f (eval_condensed d e) ->
    seq_equiv all_versions seq_f (eval_condensed d (TransformRepr env env' e)).
Proof.
  intros all_versions d e env env' seq_f H.
  (* eval_condensed d (TransformRepr env env' e) reduces to eval_condensed d e *)
  simpl. exact H.
Qed.
