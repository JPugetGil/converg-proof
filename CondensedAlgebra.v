(** * CondensedAlgebra: Condensed SPARQL Algebra Operators
    
    This module defines the condensed SPARQL algebra operators
    for efficiently querying versioned RDF datasets.
*)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.FlatAlgebra.
Import ListNotations.

(** Helper to check if a list is empty. *)
Definition is_empty {A : Type} (l : list A) : bool :=
  match l with
  | [] => true
  | _ => false
  end.

(** ** Condensed Algebra Expressions *)

(** The condensed SPARQL algebra mirrors the flat algebra
    but operates on condensed representations. *)
Inductive CondensedExpr : Type :=
  (** Quad pattern: QP_C(?s, ?p, ?o, ?g) 
      Returns condensed bindings with version sets. *)
  | QuadPatternC : Var -> Var -> Var -> Var -> CondensedExpr
  
  (** Join: ⋈_C(e1, e2)
      Intersects version sets for shared graph variables. *)
  | JoinC : CondensedExpr -> CondensedExpr -> CondensedExpr
  
  (** Filter: σ_C(E, c) *)
  | FilterC : Condition -> CondensedExpr -> CondensedExpr
  
  (** Union: ∪_C(e1, e2) *)
  | UnionC : CondensedExpr -> CondensedExpr -> CondensedExpr
  
  (** Difference: \\_C(e1, e2, c) *)
  | DiffC : CondensedExpr -> CondensedExpr -> Condition -> CondensedExpr
  
  (** Optional (Left Outer Join): ⟕_C(e1, e2, c) *)
  | OptionalC : CondensedExpr -> CondensedExpr -> Condition -> CondensedExpr
  
  (** Group By: Gr_C(exprs, e) *)
  | GroupC : list SparqlExpr -> CondensedExpr -> CondensedExpr
  
  (** Aggregation: Agg_C(exprs, aggfunc, scalars, group)
      Uses cardinality for correct counting. *)
  | AggregationC : list SparqlExpr -> AggFunc -> CondensedExpr -> CondensedExpr
  
  (** Aggregate Join: AggJ_C(agg1, ..., aggn) *)
  | AggregateJoinC : list CondensedExpr -> CondensedExpr
  
  (** Projection: Π_C(e, vars) *)
  | ProjectionC : CondensedExpr -> list Var -> CondensedExpr
  
  (** Environment transformation: ↓_r(env → env')(e) *)
  | TransformRepr : list (Var * Representation) -> list (Var * Representation) -> 
                    CondensedExpr -> CondensedExpr.

(** ** Variable Extraction *)

(** Get all variables bound by a condensed algebra expression. *)
Fixpoint condensed_expr_vars (e : CondensedExpr) : list Var :=
  match e with
  | QuadPatternC s p o g => [s; p; o; g]
  | JoinC e1 e2 => condensed_expr_vars e1 ++ condensed_expr_vars e2
  | FilterC _ e => condensed_expr_vars e
  | UnionC e1 e2 => condensed_expr_vars e1 ++ condensed_expr_vars e2
  | DiffC e1 e2 c => condensed_expr_vars e1 ++ condensed_expr_vars e2 ++ expr_vars c
  | OptionalC e1 e2 c => condensed_expr_vars e1 ++ condensed_expr_vars e2 ++ expr_vars c
  | GroupC _ e => condensed_expr_vars e
  | AggregationC _ _ e => condensed_expr_vars e
  | AggregateJoinC aggs => flat_map condensed_expr_vars aggs
  | ProjectionC e vars => vars
  | TransformRepr _ _ e => condensed_expr_vars e
  end.

(** ** Default Representations *)

(** Default representation assignment for quad pattern variables.
    - Subject, Predicate, Object: Id
    - Graph: Condensed *)
Definition quad_pattern_repr (s p o g : Var) : list (Var * Representation) :=
  [(s, Id); (p, Id); (o, Id); (g, Condensed)].

(** ** Condensed Compatibility *)

(** Two condensed bindings for a graph variable are compatible if:
    1. The named graph identifiers are equal
    2. The version sets have non-empty intersection.
    
    For value/id variables, standard equality applies. *)

(** Condensed value: (graph_id, version_set) *)
Definition CondensedValue := (nat * VersionSet)%type.

(** Check condensed compatibility for graph variables. *)
Definition condensed_compat (cv1 cv2 : CondensedValue) : bool :=
  let (g1, vs1) := cv1 in
  let (g2, vs2) := cv2 in
  if PeanoNat.Nat.eq_dec g1 g2 then
    negb (is_empty (version_set_intersection vs1 vs2))
  else
    false.

(** ** Condensed Merge *)

(** Merge two compatible condensed values by intersecting version sets. *)
Definition condensed_merge (cv1 cv2 : CondensedValue) : CondensedValue :=
  let (g1, vs1) := cv1 in
  let (g2, vs2) := cv2 in
  (g1, version_set_intersection vs1 vs2).

(** ** Cardinality *)

(** The cardinality of a condensed solution mapping is the product
    of all version set sizes for condensed variables.
    
    card(m) = Π_{?var : Condensed} |V_{?var}| × Π_{?var : UnboundGraph} |V_{?var}|
*)
Definition cardinality_contrib (cv : CondensedValue) : nat :=
  version_set_card (snd cv).

(** ** Typing for Condensed Algebra *)

(** The condensed algebra uses the same typing rules as the flat algebra,
    but the quad pattern assigns Condensed representation to graph variables. *)
Inductive condensed_expr_typing : list (Var * Representation) -> CondensedExpr -> Prop :=
  (** Quad pattern assigns Id to s,p,o and Condensed to g *)
  | TyCQuadPattern : forall env s p o g,
      condensed_expr_typing env (QuadPatternC s p o g)
      
  (** Join *)
  | TyCJoin : forall env e1 e2,
      condensed_expr_typing env e1 ->
      condensed_expr_typing env e2 ->
      condensed_expr_typing env (JoinC e1 e2)
      
  (** Filter requires Value for condition *)
  | TyCFilter : forall env c e,
      expr_typing env c Value ->
      condensed_expr_typing env e ->
      condensed_expr_typing env (FilterC c e)
      
  (** Union *)
  | TyCUnion : forall env e1 e2,
      condensed_expr_typing env e1 ->
      condensed_expr_typing env e2 ->
      condensed_expr_typing env (UnionC e1 e2)
      
  (** Representation transformation preserves typing *)
  | TyCTransform : forall env1 env2 e,
      condensed_expr_typing env1 e ->
      env1 <=_env env2 ->
      condensed_expr_typing env2 (TransformRepr env1 env2 e).
