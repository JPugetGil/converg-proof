(** * CondensedEvaluation: Semantics of the Condensed Algebra

    Thesis, Section 5.3: evaluation ⟦e⟧_C(d_C) of a condensed expression
    over a condensed model.  Quad patterns bind s, p, o in representation
    ι (identifiers) and the graph variable in representation ζ (named
    graph, version set).
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Models.
Require Import ConVerG.Representations.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Require Import ConVerG.Promotion.
Require Import ConVerG.Difference.
Require Import ConVerG.FlatAlgebra.
Require Import ConVerG.CondensedAlgebra.
Require Import ConVerG.FlatEvaluation.
Import ListNotations.

(** ** Quad pattern matching (Definition 5.27) *)

(** Dictionary encoding of the bindings of a flat mapping. *)
Definition encode (f : FMapping) : CMapping :=
  map (fun xt => (fst xt, BId (val_to_id (snd xt)))) f.

Definition match_term_c (pt : PatTerm) (t : Term) : option CMapping :=
  match match_term pt t with
  | Some f => Some (encode f)
  | None => None
  end.

(** Matching a quad pattern against an entry (q, V) of the condensed
    model: the graph variable is bound to the ζ binding (g, V). *)
Definition match_cond (s p o : PatTerm) (g : Var) (qvs : Quad * VersionSet)
  : option CMapping :=
  match match_term_c s (TermIRI (quad_subject (fst qvs))),
        match_term_c p (TermIRI (quad_predicate (fst qvs))),
        match_term_c o (quad_object (fst qvs)) with
  | Some ms, Some mp, Some mo =>
      Some (ms ++ mp ++ mo ++ [(g, BCond (quad_graph (fst qvs)) (snd qvs))])
  | _, _, _ => None
  end.

(** ** Operators *)

(** ⋈_C: pairs of compatible mappings are merged (Definition 5.28). *)
Definition join_cond (M1 M2 : list CMapping) : list CMapping :=
  flat_map (fun m1 =>
    filter_map (fun m2 =>
      if compat_cond m1 m2 then Some (merge_cond m1 m2) else None) M2) M1.

Definition filter_cond (c : SparqlExpr) (M : list CMapping) : list CMapping :=
  filter (fun m => cond_holds (lk_c m) c) M.

Definition extend_cond (x : Var) (e : SparqlExpr) (m : CMapping) : CMapping :=
  match eval_expr (lk_c m) e with
  | Some t => (x, BVal t) :: m
  | None => m
  end.

Definition optional_cond (c : SparqlExpr) (M1 M2 : list CMapping)
  : list CMapping :=
  filter_cond c (join_cond M1 M2) ++ diff_cond c M1 M2.

(** ** Evaluation *)

Fixpoint eval_cond (e : CondExpr) (dC : CondensedModel) : list CMapping :=
  match e with
  | QuadPatternC s p o g => filter_map (match_cond s p o g) dC
  | JoinC e1 e2 => join_cond (eval_cond e1 dC) (eval_cond e2 dC)
  | FilterC c e => filter_cond c (eval_cond e dC)
  | UnionC e1 e2 => eval_cond e1 dC ++ eval_cond e2 dC
  | DiffC e1 e2 c => diff_cond c (eval_cond e1 dC) (eval_cond e2 dC)
  | OptionalC e1 e2 c => optional_cond c (eval_cond e1 dC) (eval_cond e2 dC)
  | ExtendC x ex e => map (extend_cond x ex) (eval_cond e dC)
  | ProjectionC e vars => map (restrict vars) (eval_cond e dC)
  | TransformReprC reqs e => promote_seq reqs (eval_cond e dC)
  end.

(** ** Cardinality of a condensed result (Definition 5.39) *)

(** The number of flat solutions represented by a condensed sequence. *)
Definition count_condensed (M : list CMapping) : nat :=
  fold_right (fun m n => cardinality m + n) 0 M.

Lemma count_condensed_expand : forall M,
  length (flat_map expand M) = count_condensed M.
Proof.
  intros M. rewrite length_flat_map_sum. induction M as [|m M IH]; simpl;
    [reflexivity|].
  rewrite IH, expand_length. reflexivity.
Qed.
