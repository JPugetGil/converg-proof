(** * CondensedAlgebra: Syntax of the Condensed SPARQL Algebra

    Thesis, Section 5.3 (Definitions 5.27–5.37).  The condensed algebra
    mirrors the flat algebra over condensed (typed) solution mappings and
    adds the representation transformation operator Υ
    ([TransformReprC], Definition 5.36), which promotes the
    representation of some variables.
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.Representations.
Require Import ConVerG.Expressions.
Require Import ConVerG.FlatAlgebra.
Import ListNotations.

Inductive CondExpr : Type :=
  | QuadPatternC : PatTerm -> PatTerm -> PatTerm -> Var -> CondExpr
      (** QP_C(s, p, o, ?g) *)
  | JoinC : CondExpr -> CondExpr -> CondExpr
      (** ⋈_C(e1, e2) *)
  | FilterC : SparqlExpr -> CondExpr -> CondExpr
      (** σ_C(c, e) *)
  | UnionC : CondExpr -> CondExpr -> CondExpr
      (** ∪_C(e1, e2) *)
  | DiffC : CondExpr -> CondExpr -> SparqlExpr -> CondExpr
      (** \_C(e1, e2, c) *)
  | OptionalC : CondExpr -> CondExpr -> SparqlExpr -> CondExpr
      (** ⟕_C(e1, e2, c) *)
  | ExtendC : Var -> SparqlExpr -> CondExpr -> CondExpr
      (** ρ_C(?x, expr, e) *)
  | ProjectionC : CondExpr -> list Var -> CondExpr
      (** Π_C(e, vars) *)
  | TransformReprC : list (Var * Representation) -> CondExpr -> CondExpr.
      (** Υ_reqs(e): promote the variables of [reqs] *)
