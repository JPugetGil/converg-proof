(** * SolutionMappings: Solution Mapping Definitions
    
    This module defines solution mappings for both flat and condensed
    algebra evaluation, including compatibility and merge functions.
*)

Require Import Stdlib.Lists.List.
Require Import ConVerG.RDF.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.Translation.
Import ListNotations.

(** ** Solution Mapping Types *)

(** A solution mapping component stores a variable binding with its representation.
    The value type depends on the representation:
    - Value: Term
    - Id: nat (term identifier)
    - Condensed: (nat, VersionSet) (graph id, version set)
    - UnboundGraph: unit (the special • symbol)
*)

(** Value in Value representation. *)
Definition ValueBinding := (Var * Term)%type.

(** Value in Id representation. *)
Definition IdBinding := (Var * nat)%type.

(** Value in Condensed representation: (graph_id, version_set). *)
Definition CondensedBinding := (Var * (nat * VersionSet))%type.

(** Value in UnboundGraph representation. *)
Definition UnboundGraphBinding := Var.

(** A complete solution mapping has components for each representation. *)
Record SolutionMapping : Type := mkSolutionMapping {
  m_value : list ValueBinding;
  m_id : list IdBinding;
  m_condensed : list CondensedBinding;
  m_unboundgraph : list UnboundGraphBinding
}.

(** Empty solution mapping. *)
Definition empty_mapping : SolutionMapping :=
  mkSolutionMapping [] [] [] [].

(** ** Domain Functions *)

Definition domain_value (m : SolutionMapping) : list Var :=
  map fst (m_value m).

Definition domain_id (m : SolutionMapping) : list Var :=
  map fst (m_id m).

Definition domain_condensed (m : SolutionMapping) : list Var :=
  map fst (m_condensed m).

Definition domain_unboundgraph (m : SolutionMapping) : list Var :=
  m_unboundgraph m.

Definition domain_all (m : SolutionMapping) : list Var :=
  domain_value m ++ domain_id m ++ domain_condensed m ++ domain_unboundgraph m.

(** ** Lookup Functions *)

Fixpoint lookup_value (x : Var) (bindings : list ValueBinding) : option Term :=
  match bindings with
  | [] => None
  | (y, t) :: rest => if Var_eq_dec x y then Some t else lookup_value x rest
  end.

Fixpoint lookup_id (x : Var) (bindings : list IdBinding) : option nat :=
  match bindings with
  | [] => None
  | (y, n) :: rest => if Var_eq_dec x y then Some n else lookup_id x rest
  end.

Fixpoint lookup_condensed (x : Var) (bindings : list CondensedBinding) 
         : option (nat * VersionSet) :=
  match bindings with
  | [] => None
  | (y, cv) :: rest => if Var_eq_dec x y then Some cv else lookup_condensed x rest
  end.

(** ** vals Function *)

(** Abstract function mapping (version, graph_id) to a Term.
    This corresponds to the VI function in the paper:
    VI(v, g) returns the versioned IRI for named graph g at version v. *)
Parameter vi_to_term : Version -> nat -> Term.

(** The set of all versioned named graphs, parameterized by versions and graph ids.
    In a full implementation this would enumerate all (v, g) pairs. *)
Parameter all_versioned_named_graphs : VersionSet -> list nat -> list Term.

(** The vals function returns the set of terms for a variable in a mapping.
    vals_m(?var) depends on the representation of the variable:
    - Value: the single bound term
    - Id: the term obtained from the identifier via id_to_val
    - Condensed (g, V): { VI(v, g) | v ∈ V }
    - UnboundGraph: all versioned named graphs
*)
Definition vals (m : SolutionMapping) (x : Var) : list Term :=
  match lookup_value x (m_value m) with
  | Some t => [t]
  | None =>
    match lookup_id x (m_id m) with
    | Some n => [id_to_val n]
    | None =>
      match lookup_condensed x (m_condensed m) with
      | Some (g, vs) =>
        map (fun v => vi_to_term v g) vs
      | None =>
        [] (* Variable not in mapping domain *)
      end
    end
  end.

(** ** Flat Compatibility *)

(** Two flat solution mappings are compatible if they agree on shared variables.
    m1 ∼_F m2 ⟺ ∀?var ∈ dom(m1) ∩ dom(m2), m1(?var) = m2(?var)
*)
Definition compatible_flat (m1 m2 : SolutionMapping) : Prop :=
  forall x t1 t2,
    lookup_value x (m_value m1) = Some t1 ->
    lookup_value x (m_value m2) = Some t2 ->
    t1 = t2.

(** Boolean version of flat compatibility (simplified). *)
Definition compatible_flat_dec (m1 m2 : SolutionMapping) : bool :=
  forallb (fun xv : Var * Term =>
    match lookup_value (fst xv) (m_value m2) with
    | Some v2 => if Term_eq_dec (snd xv) v2 then true else false
    | None => true
    end
  ) (m_value m1).

(** ** Flat Merge *)

(** Merge two compatible flat solution mappings.
    ∪_F(m1, m2)(x) = m1(x) if x ∈ dom(m1), else m2(x)
*)
Definition merge_flat (m1 m2 : SolutionMapping) : SolutionMapping :=
  mkSolutionMapping
    (m_value m1 ++ filter (fun xv => negb (set_member Var_eq_dec (fst xv) (domain_value m1))) (m_value m2))
    (m_id m1 ++ filter (fun xv => negb (set_member Var_eq_dec (fst xv) (domain_id m1))) (m_id m2))
    (m_condensed m1 ++ filter (fun xv => negb (set_member Var_eq_dec (fst xv) (domain_condensed m1))) (m_condensed m2))
    (m_unboundgraph m1 ++ filter (fun x => negb (set_member Var_eq_dec x (m_unboundgraph m1))) (m_unboundgraph m2)).

(** ** Condensed Compatibility *)

(** Two condensed solution mappings are compatible if:
    - Value/Id variables: values are equal
    - Condensed variables: graph ids equal AND version sets have non-empty intersection
    - UnboundGraph variables: always compatible
*)
Definition compatible_condensed (m1 m2 : SolutionMapping) : Prop :=
  (* Value compatibility *)
  (forall x t1 t2,
    lookup_value x (m_value m1) = Some t1 ->
    lookup_value x (m_value m2) = Some t2 ->
    t1 = t2) /\
  (* Id compatibility *)
  (forall x n1 n2,
    lookup_id x (m_id m1) = Some n1 ->
    lookup_id x (m_id m2) = Some n2 ->
    n1 = n2) /\
  (* Condensed compatibility: same graph, non-empty version intersection *)
  (forall x g1 vs1 g2 vs2,
    lookup_condensed x (m_condensed m1) = Some (g1, vs1) ->
    lookup_condensed x (m_condensed m2) = Some (g2, vs2) ->
    g1 = g2 /\ version_set_intersection vs1 vs2 <> []).

(** ** Condensed Merge *)

(** Merge two compatible condensed solution mappings.
    For condensed variables, intersect the version sets.
*)
Definition merge_condensed_binding (c1 c2 : nat * VersionSet) : nat * VersionSet :=
  let (g1, vs1) := c1 in
  let (g2, vs2) := c2 in
  (g1, version_set_intersection vs1 vs2).

Definition merge_condensed (m1 m2 : SolutionMapping) : SolutionMapping :=
  mkSolutionMapping
    (m_value m1 ++ filter (fun xv => negb (set_member Var_eq_dec (fst xv) (domain_value m1))) (m_value m2))
    (m_id m1 ++ filter (fun xv => negb (set_member Var_eq_dec (fst xv) (domain_id m1))) (m_id m2))
    (* For condensed, need to merge with intersection *)
    (map (fun xc : Var * (nat * VersionSet) =>
      match lookup_condensed (fst xc) (m_condensed m2) with
      | Some c2 => (fst xc, merge_condensed_binding (snd xc) c2)
      | None => xc
      end
    ) (m_condensed m1) ++
    filter (fun xc => negb (set_member Var_eq_dec (fst xc) (domain_condensed m1))) (m_condensed m2))
    (m_unboundgraph m1 ++ filter (fun x => negb (set_member Var_eq_dec x (m_unboundgraph m1))) (m_unboundgraph m2)).

(** ** Cardinality *)

(** The cardinality of a solution mapping is the product of all
    version set sizes for condensed and unboundgraph variables.
    
    card(m) = Π_{x ∈ dom(m_ζ)} |V_x| × Π_{x ∈ dom(m_ψ)} |V_x|
*)
Definition mapping_cardinality (m : SolutionMapping) (all_versions : VersionSet) : nat :=
  let condensed_card := fold_right 
    (fun xc acc => acc * version_set_card (snd (snd xc)))
    1
    (m_condensed m) in
  let unboundgraph_card := fold_right
    (fun _ acc => acc * version_set_card all_versions)
    1
    (m_unboundgraph m) in
  condensed_card * unboundgraph_card.

(** ** Invariance Lemma *)

(** Two solution mappings are vals-equivalent if they produce the same
    term sets for every variable. *)
Definition vals_equiv (m1 m2 : SolutionMapping) : Prop :=
  forall x, vals m1 x = vals m2 x.

(** Lemma: vals equivalence is reflexive. *)
Lemma vals_equiv_refl : forall m, vals_equiv m m.
Proof. unfold vals_equiv. intros m x. reflexivity. Qed.

(** Lemma: vals equivalence is symmetric. *)
Lemma vals_equiv_sym : forall m1 m2, vals_equiv m1 m2 -> vals_equiv m2 m1.
Proof. unfold vals_equiv. intros m1 m2 H x. symmetry. apply H. Qed.

(** Lemma: vals equivalence is transitive. *)
Lemma vals_equiv_trans : forall m1 m2 m3,
  vals_equiv m1 m2 -> vals_equiv m2 m3 -> vals_equiv m1 m3.
Proof.
  unfold vals_equiv. intros m1 m2 m3 H12 H23 x.
  rewrite H12. apply H23.
Qed.

(** Lemma: If two value-only mappings agree on all value bindings,
    they are vals-equivalent. *)
Lemma value_bindings_determine_vals :
  forall m1 m2 : SolutionMapping,
    m_id m1 = [] -> m_id m2 = [] ->
    m_condensed m1 = [] -> m_condensed m2 = [] ->
    m_unboundgraph m1 = [] -> m_unboundgraph m2 = [] ->
    (forall x, lookup_value x (m_value m1) = lookup_value x (m_value m2)) ->
    vals_equiv m1 m2.
Proof.
  unfold vals_equiv, vals.
  intros m1 m2 Hid1 Hid2 Hc1 Hc2 Hu1 Hu2 Hval x.
  rewrite Hval.
  destruct (lookup_value x (m_value m2)); [reflexivity|].
  rewrite Hid1, Hid2. simpl.
  rewrite Hc1, Hc2. simpl.
  reflexivity.
Qed.
