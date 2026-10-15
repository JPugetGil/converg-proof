(** * Translation: From the Flat Algebra to the Condensed Algebra

    Thesis, Section 5.5 (translation function τ and optimal
    representation function R-star, Definitions 5.40–5.41).

    [translate e] returns the condensed expression τ(e) together with its
    result environment R(e).  The environment records, for every variable
    that may be bound, the least representation its bindings can have.
    A promotion Υ is inserted before every operator that needs
    point-valued variables:
    - FILTER, BIND and the conditions of DIFF and OPTIONAL need the
      variables of their expression at the representations required by
      Definition 5.43 ([cond_reqs], [bind_reqs]: ν under a function,
      ι under an equality or at the top of a BIND, ν at the top of a
      condition);
    - PROJECTION needs the variables it drops in ι (or above): dropping
      a ζ variable would otherwise lose the multiplicity of its versions
      (see Equivalence.v, [projection_perm]).  This requirement is
      missing from the thesis's rule for Π_C.
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Require Import ConVerG.Aggregation.
Require Import ConVerG.Typing.
Require Import ConVerG.FlatAlgebra.
Require Import ConVerG.CondensedAlgebra.
Import ListNotations.

(** The environment of a quad pattern: s, p, o in ι and the graph
    variable, if any, in ζ (Definition 5.44, rule QuadPattern). *)
Definition pat_env (s p o g : PatTerm) : Environment :=
  map (fun x => (x, Id)) (pat_vars s ++ pat_vars p ++ pat_vars o)
  ++ map (fun x => (x, Condensed)) (pat_vars g).

(** The variables of [env] that are not projected. *)
Definition dropped_vars (env : Environment) (vars : list Var) : list Var :=
  filter (fun y => negb (memb y vars)) (env_domain env).

(** The requirements of a GROUP BY (Definition 5.44, rules Group and
    Aggregation): grouping variables at ι, variables of the aggregated
    expressions at the representations of their conditions (ν under a
    function). *)
Definition groupagg_reqs (ks : list Var) (aggs : list Aggregate)
  : list (Var * Representation) :=
  map (fun x => (x, Id)) ks ++ flat_map (fun ag => cond_reqs (agg_expr ag)) aggs.

(** The environment of the solutions of a GROUP BY: the grouping variables
    that may be bound and the aggregate variables, all in ν. *)
Definition groupagg_env (env : Environment) (ks : list Var)
  (aggs : list Aggregate) : Environment :=
  map (fun x => (x, Value)) (filter (fun x => in_env_domain x env) ks)
  ++ map (fun ag => (agg_var ag, Value)) aggs.

Fixpoint translate (e : FlatExpr) : CondExpr * Environment :=
  match e with
  | QuadPatternF s p o g => (QuadPatternC s p o g, pat_env s p o g)
  | JoinF e1 e2 =>
      let (c1, env1) := translate e1 in
      let (c2, env2) := translate e2 in
      (JoinC c1 c2, env_meet env1 env2)
  | FilterF c e =>
      let (c1, env1) := translate e in
      let reqs := needs_reqs env1 (cond_reqs c) in
      (FilterC c (TransformReprC reqs c1), env_raise env1 reqs)
  | UnionF e1 e2 =>
      let (c1, env1) := translate e1 in
      let (c2, env2) := translate e2 in
      (UnionC c1 c2, env_meet env1 env2)
  | DiffF e1 e2 c =>
      let (c1, env1) := translate e1 in
      let (c2, env2) := translate e2 in
      let reqs1 := needs_reqs env1 (cond_reqs c) in
      let reqs2 := needs_reqs env2 (cond_reqs c) in
      (DiffC (TransformReprC reqs1 c1) (TransformReprC reqs2 c2) c,
       env_raise env1 reqs1)
  | OptionalF e1 e2 c =>
      let (c1, env1) := translate e1 in
      let (c2, env2) := translate e2 in
      let reqs1 := needs_reqs env1 (cond_reqs c) in
      let reqs2 := needs_reqs env2 (cond_reqs c) in
      (OptionalC (TransformReprC reqs1 c1) (TransformReprC reqs2 c2) c,
       env_meet (env_raise env1 reqs1) (env_raise env2 reqs2))
  | ExtendF x ex e =>
      let (c1, env1) := translate e in
      let reqs := needs_reqs env1 (bind_reqs ex) in
      (ExtendC x ex (TransformReprC reqs c1),
       (x, Value) :: env_raise env1 reqs)
  | ProjectionF e vars =>
      let (c1, env1) := translate e in
      let reqs := needs env1 (dropped_vars env1 vars) Id in
      (ProjectionC (TransformReprC reqs c1) vars,
       env_restrict (env_raise env1 reqs) vars)
  | GroupAggF ks aggs e =>
      let (c1, env1) := translate e in
      let reqs := needs_reqs env1 (groupagg_reqs ks aggs) in
      (GroupAggC ks aggs (TransformReprC reqs c1),
       groupagg_env (env_raise env1 reqs) ks aggs)
  | GraphsF x => (GraphsC x, [(x, UnboundGraph)])
  end.

(** τ(e) and R(e). *)
Definition translate_expr (e : FlatExpr) : CondExpr := fst (translate e).
Definition result_env (e : FlatExpr) : Environment := snd (translate e).

(** Unfolding equations of [translate], one per operator. *)

Lemma translate_qp : forall s p o g,
  translate (QuadPatternF s p o g) = (QuadPatternC s p o g, pat_env s p o g).
Proof. reflexivity. Qed.

Lemma translate_join : forall e1 e2,
  translate (JoinF e1 e2) =
  (JoinC (fst (translate e1)) (fst (translate e2)),
   env_meet (snd (translate e1)) (snd (translate e2))).
Proof.
  intros e1 e2. simpl. destruct (translate e1), (translate e2). reflexivity.
Qed.

Lemma translate_filter : forall c e,
  translate (FilterF c e) =
  (FilterC c (TransformReprC (needs_reqs (snd (translate e)) (cond_reqs c))
                             (fst (translate e))),
   env_raise (snd (translate e)) (needs_reqs (snd (translate e)) (cond_reqs c))).
Proof. intros c e. simpl. destruct (translate e). reflexivity. Qed.

Lemma translate_union : forall e1 e2,
  translate (UnionF e1 e2) =
  (UnionC (fst (translate e1)) (fst (translate e2)),
   env_meet (snd (translate e1)) (snd (translate e2))).
Proof.
  intros e1 e2. simpl. destruct (translate e1), (translate e2). reflexivity.
Qed.

Lemma translate_diff : forall e1 e2 c,
  translate (DiffF e1 e2 c) =
  (DiffC (TransformReprC (needs_reqs (snd (translate e1)) (cond_reqs c))
                         (fst (translate e1)))
         (TransformReprC (needs_reqs (snd (translate e2)) (cond_reqs c))
                         (fst (translate e2))) c,
   env_raise (snd (translate e1)) (needs_reqs (snd (translate e1)) (cond_reqs c))).
Proof.
  intros e1 e2 c. simpl. destruct (translate e1), (translate e2). reflexivity.
Qed.

Lemma translate_optional : forall e1 e2 c,
  translate (OptionalF e1 e2 c) =
  (OptionalC (TransformReprC (needs_reqs (snd (translate e1)) (cond_reqs c))
                             (fst (translate e1)))
             (TransformReprC (needs_reqs (snd (translate e2)) (cond_reqs c))
                             (fst (translate e2))) c,
   env_meet
     (env_raise (snd (translate e1)) (needs_reqs (snd (translate e1)) (cond_reqs c)))
     (env_raise (snd (translate e2)) (needs_reqs (snd (translate e2)) (cond_reqs c)))).
Proof.
  intros e1 e2 c. simpl. destruct (translate e1), (translate e2). reflexivity.
Qed.

Lemma translate_extend : forall x ex e,
  translate (ExtendF x ex e) =
  (ExtendC x ex (TransformReprC (needs_reqs (snd (translate e)) (bind_reqs ex))
                                (fst (translate e))),
   (x, Value) :: env_raise (snd (translate e))
                           (needs_reqs (snd (translate e)) (bind_reqs ex))).
Proof. intros x ex e. simpl. destruct (translate e). reflexivity. Qed.

Lemma translate_projection : forall e vars,
  translate (ProjectionF e vars) =
  (ProjectionC (TransformReprC
                  (needs (snd (translate e)) (dropped_vars (snd (translate e)) vars) Id)
                  (fst (translate e))) vars,
   env_restrict
     (env_raise (snd (translate e))
                (needs (snd (translate e)) (dropped_vars (snd (translate e)) vars) Id))
     vars).
Proof. intros e vars. simpl. destruct (translate e). reflexivity. Qed.

Lemma translate_groupagg : forall ks aggs e,
  translate (GroupAggF ks aggs e) =
  (GroupAggC ks aggs
     (TransformReprC (needs_reqs (snd (translate e)) (groupagg_reqs ks aggs))
                     (fst (translate e))),
   groupagg_env
     (env_raise (snd (translate e))
                (needs_reqs (snd (translate e)) (groupagg_reqs ks aggs)))
     ks aggs).
Proof. intros ks aggs e. simpl. destruct (translate e). reflexivity. Qed.

Lemma translate_graphs : forall x,
  translate (GraphsF x) = (GraphsC x, [(x, UnboundGraph)]).
Proof. reflexivity. Qed.

Lemma groupagg_env_domain : forall env ks aggs z,
  In z (env_domain (groupagg_env env ks aggs)) ->
  In z ks \/ In z (map agg_var aggs).
Proof.
  intros env ks aggs z Hz. unfold groupagg_env, env_domain in Hz.
  rewrite map_app, !map_map in Hz. cbn [fst] in Hz. apply in_app_iff in Hz.
  destruct Hz as [Hz | Hz].
  - left. rewrite map_id in Hz. apply filter_In in Hz. tauto.
  - right. exact Hz.
Qed.

(** The result environment only mentions in-scope variables. *)
Lemma translate_domain : forall e z,
  In z (env_domain (snd (translate e))) -> In z (flat_expr_vars e).
Proof.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars
                  | ks aggs e IH | x];
    intros z Hz; cbn [flat_expr_vars].
  - rewrite translate_qp in Hz. cbn [snd] in Hz.
    unfold pat_env, env_domain in Hz. rewrite map_app, !map_map in Hz.
    cbn [fst] in Hz. rewrite !map_id in Hz. unfold quad_pat_vars.
    rewrite <- !app_assoc in Hz. exact Hz.
  - rewrite translate_join in Hz. cbn [snd] in Hz.
    apply env_meet_domain in Hz. apply in_app_iff.
    destruct Hz as [Hz | Hz]; [left; apply IH1 | right; apply IH2]; exact Hz.
  - rewrite translate_filter in Hz. cbn [snd] in Hz.
    apply IH. exact (proj1 (raise_needs_reqs_domain _ _ _) Hz).
  - rewrite translate_union in Hz. cbn [snd] in Hz.
    apply env_meet_domain in Hz. apply in_app_iff.
    destruct Hz as [Hz | Hz]; [left; apply IH1 | right; apply IH2]; exact Hz.
  - rewrite translate_diff in Hz. cbn [snd] in Hz.
    apply IH1. exact (proj1 (raise_needs_reqs_domain _ _ _) Hz).
  - rewrite translate_optional in Hz. cbn [snd] in Hz.
    apply env_meet_domain in Hz. apply in_app_iff.
    destruct Hz as [Hz | Hz].
    + left. apply IH1. exact (proj1 (raise_needs_reqs_domain _ _ _) Hz).
    + right. apply IH2. exact (proj1 (raise_needs_reqs_domain _ _ _) Hz).
  - rewrite translate_extend in Hz. cbn [snd] in Hz.
    destruct Hz as [<- | Hz]; [left; reflexivity|].
    right. apply IH. exact (proj1 (raise_needs_reqs_domain _ _ _) Hz).
  - rewrite translate_projection in Hz. cbn [snd] in Hz.
    unfold env_restrict, env_domain in Hz.
    apply in_map_iff in Hz. destruct Hz as [[y r] [<- Hy]].
    apply filter_In in Hy. destruct Hy as [_ Hy]. cbn [fst] in Hy.
    apply inb_true_iff in Hy. exact Hy.
  - rewrite translate_groupagg in Hz. cbn [snd] in Hz.
    apply in_app_iff. eapply groupagg_env_domain. exact Hz.
  - rewrite translate_graphs in Hz. cbn [snd] in Hz.
    destruct Hz as [<- | []]. left. reflexivity.
Qed.
