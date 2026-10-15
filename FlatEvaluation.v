(** * FlatEvaluation: Semantics of the Flat Algebra

    Thesis, Section 5.2: evaluation ⟦e⟧_F(d_F) of a flat expression over a
    flat model, under bag semantics (solution sequences are lists; the
    order is irrelevant, see [Permutation] in Equivalence.v).
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Models.
Require Import ConVerG.Representations.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Require Import ConVerG.Difference.
Require Import ConVerG.FlatAlgebra.
Import ListNotations.

(** ** Quad pattern matching (Definition 5.9) *)

(** Matching one pattern position against a term: a variable is bound,
    a constant must be equal. *)
Definition match_term (pt : PatTerm) (t : Term) : option FMapping :=
  match pt with
  | PVar x => Some [(x, t)]
  | PConst t' => if Term_eq_dec t t' then Some [] else None
  end.

(** Matching a quad pattern against a versioned quad (s, p, o, g, v): the
    graph variable is bound to the versioned IRI VI(v, g). *)
Definition match_flat (s p o : PatTerm) (g : Var) (vq : VersionedQuad)
  : option FMapping :=
  match match_term s (TermIRI (vq_subject vq)),
        match_term p (TermIRI (vq_predicate vq)),
        match_term o (vq_object vq) with
  | Some fs, Some fp, Some fo =>
      Some (fs ++ fp ++ fo ++
            [(g, TermIRI (vi (vq_version vq) (vq_graph vq)))])
  | _, _, _ => None
  end.

(** ** Operators *)

Definition filter_flat (c : SparqlExpr) (L : list FMapping) : list FMapping :=
  filter (fun f => cond_holds (lk_f f) c) L.

(** BIND: the new variable is bound when the expression evaluates without
    error. *)
Definition extend_flat (x : Var) (e : SparqlExpr) (f : FMapping) : FMapping :=
  match eval_expr (lk_f f) e with
  | Some t => (x, t) :: f
  | None => f
  end.

(** Left outer join = filtered join ∪ difference (Definition 5.13). *)
Definition optional_flat (c : SparqlExpr) (L1 L2 : list FMapping)
  : list FMapping :=
  filter_flat c (join_flat L1 L2) ++ diff_flat c L1 L2.

(** ** Evaluation *)

Fixpoint eval_flat (e : FlatExpr) (dF : FlatModel) : list FMapping :=
  match e with
  | QuadPatternF s p o g => filter_map (match_flat s p o g) dF
  | JoinF e1 e2 => join_flat (eval_flat e1 dF) (eval_flat e2 dF)
  | FilterF c e => filter_flat c (eval_flat e dF)
  | UnionF e1 e2 => eval_flat e1 dF ++ eval_flat e2 dF
  | DiffF e1 e2 c => diff_flat c (eval_flat e1 dF) (eval_flat e2 dF)
  | OptionalF e1 e2 c => optional_flat c (eval_flat e1 dF) (eval_flat e2 dF)
  | ExtendF x ex e => map (extend_flat x ex) (eval_flat e dF)
  | ProjectionF e vars => map (restrict vars) (eval_flat e dF)
  end.
