(** * FlatAlgebra: Flat SPARQL Algebra Operators
    
    This module defines the flat SPARQL algebra operators
    for querying versioned RDF datasets.
*)

From Stdlib Require Import List.
Require Import ConVerG.RDF.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Import ListNotations.

(** ** Expressions and Conditions *)

(** SPARQL expressions (for FILTER, GROUP BY, etc.) *)
Inductive SparqlExpr : Type :=
  | ExprTerm : Term -> SparqlExpr              (** Constant term *)
  | ExprVar : Var -> SparqlExpr                (** Variable reference *)
  | ExprFunc : nat -> list SparqlExpr -> SparqlExpr (** Function application *)
  | ExprEq : SparqlExpr -> SparqlExpr -> SparqlExpr  (** Equality test *)
  | ExprNeq : SparqlExpr -> SparqlExpr -> SparqlExpr (** Inequality test *)
  | ExprAnd : SparqlExpr -> SparqlExpr -> SparqlExpr (** Logical AND *)
  | ExprOr : SparqlExpr -> SparqlExpr -> SparqlExpr  (** Logical OR *)
  | ExprNot : SparqlExpr -> SparqlExpr.              (** Logical NOT *)

(** Filter conditions are SPARQL expressions that evaluate to boolean. *)
Definition Condition := SparqlExpr.

(** ** Aggregation Functions *)

(** Supported aggregation functions. *)
Inductive AggFunc : Type :=
  | AggCount
  | AggSum
  | AggAvg
  | AggMin
  | AggMax
  | AggGroupConcat (separator : option Term)
  | AggSample.

(** ** Flat Algebra Expressions *)

(** The flat SPARQL algebra. *)
Inductive FlatExpr : Type :=
  (** Quad pattern: QP_F(?s, ?p, ?o, ?g) *)
  | QuadPatternF : Var -> Var -> Var -> Var -> FlatExpr
  
  (** Join: ⋈_F(e1, e2) *)
  | JoinF : FlatExpr -> FlatExpr -> FlatExpr
  
  (** Filter: σ_F(E, c) *)
  | FilterF : Condition -> FlatExpr -> FlatExpr
  
  (** Union: ∪_F(e1, e2) *)
  | UnionF : FlatExpr -> FlatExpr -> FlatExpr
  
  (** Difference: \\_F(e1, e2, c) *)
  | DiffF : FlatExpr -> FlatExpr -> Condition -> FlatExpr
  
  (** Optional (Left Outer Join): ⟕_F(e1, e2, c) *)
  | OptionalF : FlatExpr -> FlatExpr -> Condition -> FlatExpr
  
  (** Group By: Gr_F(exprs, e) *)
  | GroupF : list SparqlExpr -> FlatExpr -> FlatExpr
  
  (** Aggregation: Agg_F(exprs, aggfunc, scalars, group) *)
  | AggregationF : list SparqlExpr -> AggFunc -> FlatExpr -> FlatExpr
  
  (** Aggregate Join: AggJ_F(agg1, ..., aggn) *)
  | AggregateJoinF : list FlatExpr -> FlatExpr
  
  (** Projection: Π_F(e, vars) *)
  | ProjectionF : FlatExpr -> list Var -> FlatExpr.

(** ** Variable Extraction *)

(** Get all variables used in a SPARQL expression. *)
Fixpoint expr_vars (e : SparqlExpr) : list Var :=
  match e with
  | ExprTerm _ => []
  | ExprVar x => [x]
  | ExprFunc _ args => flat_map expr_vars args
  | ExprEq e1 e2 => expr_vars e1 ++ expr_vars e2
  | ExprNeq e1 e2 => expr_vars e1 ++ expr_vars e2
  | ExprAnd e1 e2 => expr_vars e1 ++ expr_vars e2
  | ExprOr e1 e2 => expr_vars e1 ++ expr_vars e2
  | ExprNot e1 => expr_vars e1
  end.

(** Get all variables bound by a flat algebra expression. *)
Fixpoint flat_expr_vars (e : FlatExpr) : list Var :=
  match e with
  | QuadPatternF s p o g => [s; p; o; g]
  | JoinF e1 e2 => flat_expr_vars e1 ++ flat_expr_vars e2
  | FilterF _ e => flat_expr_vars e
  | UnionF e1 e2 => flat_expr_vars e1 ++ flat_expr_vars e2
  | DiffF e1 e2 c => flat_expr_vars e1 ++ flat_expr_vars e2 ++ expr_vars c
  | OptionalF e1 e2 c => flat_expr_vars e1 ++ flat_expr_vars e2 ++ expr_vars c
  | GroupF _ e => flat_expr_vars e
  | AggregationF _ _ e => flat_expr_vars e
  | AggregateJoinF aggs => flat_map flat_expr_vars aggs
  | ProjectionF e vars => vars
  end.

(** ** Typing Rules *)

(** Expression typing: Γ ⊢ e : r *)
Inductive expr_typing : list (Var * Representation) -> SparqlExpr -> Representation -> Prop :=
  (** Terms are always Value *)
  | TyTerm : forall env t,
      expr_typing env (ExprTerm t) Value
      
  (** Variables get their representation from the environment *)
  | TyVar : forall env x r,
      env_lookup x env = Some r ->
      expr_typing env (ExprVar x) r
      
  (** Functions require Value arguments and produce Value *)
  | TyFunc : forall env f args,
      Forall (fun e => expr_typing env e Value) args ->
      expr_typing env (ExprFunc f args) Value
      
  (** Equality requires at least Id representation *)
  | TyEq : forall env e1 e2 r,
      Id <=_r r ->
      expr_typing env e1 r ->
      expr_typing env e2 r ->
      expr_typing env (ExprEq e1 e2) Value
      
  (** Logical operators require Value *)
  | TyAnd : forall env e1 e2,
      expr_typing env e1 Value ->
      expr_typing env e2 Value ->
      expr_typing env (ExprAnd e1 e2) Value.

(** Operator typing: Γ ⊢ E *)
Inductive flat_expr_typing : list (Var * Representation) -> FlatExpr -> Prop :=
  (** Quad pattern with IRI graph *)
  | TyQuadPatternIRI : forall env s p o g,
      flat_expr_typing env (QuadPatternF s p o g)
      
  (** Join requires both subexpressions to be well-typed *)
  | TyJoin : forall env e1 e2,
      flat_expr_typing env e1 ->
      flat_expr_typing env e2 ->
      flat_expr_typing env (JoinF e1 e2)
      
  (** Filter requires condition to be Value *)
  | TyFilter : forall env c e,
      expr_typing env c Value ->
      flat_expr_typing env e ->
      flat_expr_typing env (FilterF c e)
      
  (** Union requires both subexpressions *)
  | TyUnion : forall env e1 e2,
      flat_expr_typing env e1 ->
      flat_expr_typing env e2 ->
      flat_expr_typing env (UnionF e1 e2)
      
  (** Group requires grouping expressions to be Value *)
  | TyGroup : forall env exprs e,
      Forall (fun exp => expr_typing env exp Value) exprs ->
      flat_expr_typing env e ->
      flat_expr_typing env (GroupF exprs e)
      
  (** Aggregation requires expressions to be Value *)
  | TyAggregation : forall env exprs agg grp,
      Forall (fun exp => expr_typing env exp Value) exprs ->
      flat_expr_typing env grp ->
      flat_expr_typing env (AggregationF exprs agg grp).
