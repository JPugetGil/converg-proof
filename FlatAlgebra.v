(** * FlatAlgebra: Syntax of the Flat SPARQL Algebra

    Thesis, Section 5.2 (Definitions 5.9–5.17).  The flat algebra is the
    standard SPARQL algebra evaluated over the flat model d_F, where the
    graph position of a quad pattern is bound to a versioned IRI.

    Scope: quad patterns, join, filter, union, difference, optional
    (left outer join), bind (extend) and projection.  Grouping and
    aggregation (Definitions 5.14–5.15) are outside the scope of this
    development, as is the ψ representation (unbound graph variables):
    the graph position of a quad pattern is always a variable.
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Import ListNotations.

(** ** Pattern terms *)

Inductive PatTerm : Type :=
  | PVar : Var -> PatTerm
  | PConst : Term -> PatTerm.

Definition pat_vars (pt : PatTerm) : list Var :=
  match pt with
  | PVar x => [x]
  | PConst _ => []
  end.

(** The variables of a quad pattern, in binding order. *)
Definition quad_pat_vars (s p o : PatTerm) (g : Var) : list Var :=
  pat_vars s ++ pat_vars p ++ pat_vars o ++ [g].

(** ** Flat algebra expressions *)

Inductive FlatExpr : Type :=
  | QuadPatternF : PatTerm -> PatTerm -> PatTerm -> Var -> FlatExpr
      (** QP_F(s, p, o, ?g) *)
  | JoinF : FlatExpr -> FlatExpr -> FlatExpr
      (** ⋈_F(e1, e2) *)
  | FilterF : SparqlExpr -> FlatExpr -> FlatExpr
      (** σ_F(c, e) *)
  | UnionF : FlatExpr -> FlatExpr -> FlatExpr
      (** ∪_F(e1, e2) *)
  | DiffF : FlatExpr -> FlatExpr -> SparqlExpr -> FlatExpr
      (** \_F(e1, e2, c) *)
  | OptionalF : FlatExpr -> FlatExpr -> SparqlExpr -> FlatExpr
      (** ⟕_F(e1, e2, c) *)
  | ExtendF : Var -> SparqlExpr -> FlatExpr -> FlatExpr
      (** ρ_F(?x, expr, e): BIND *)
  | ProjectionF : FlatExpr -> list Var -> FlatExpr.
      (** Π_F(e, vars) *)

(** Variables that may be bound by the result of an expression (the
    in-scope variables). *)
Fixpoint flat_expr_vars (e : FlatExpr) : list Var :=
  match e with
  | QuadPatternF s p o g => quad_pat_vars s p o g
  | JoinF e1 e2 => flat_expr_vars e1 ++ flat_expr_vars e2
  | FilterF _ e => flat_expr_vars e
  | UnionF e1 e2 => flat_expr_vars e1 ++ flat_expr_vars e2
  | DiffF e1 _ _ => flat_expr_vars e1
  | OptionalF e1 e2 _ => flat_expr_vars e1 ++ flat_expr_vars e2
  | ExtendF x _ e => x :: flat_expr_vars e
  | ProjectionF _ vars => vars
  end.

(** Well-formed expressions: quad patterns do not repeat a variable and
    BIND introduces a fresh variable (the unique-naming assumption of the
    thesis). *)
Fixpoint wf_flat_expr (e : FlatExpr) : Prop :=
  match e with
  | QuadPatternF s p o g => NoDup (quad_pat_vars s p o g)
  | JoinF e1 e2 => wf_flat_expr e1 /\ wf_flat_expr e2
  | FilterF _ e => wf_flat_expr e
  | UnionF e1 e2 => wf_flat_expr e1 /\ wf_flat_expr e2
  | DiffF e1 e2 _ => wf_flat_expr e1 /\ wf_flat_expr e2
  | OptionalF e1 e2 _ => wf_flat_expr e1 /\ wf_flat_expr e2
  | ExtendF x _ e => ~ In x (flat_expr_vars e) /\ wf_flat_expr e
  | ProjectionF e _ => wf_flat_expr e
  end.
