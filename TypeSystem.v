(** * TypeSystem: Typing of Condensed Expressions

    Thesis, Definition 5.38 (type system Γ ⊢ E_C ⇒ Γ').  A condensed
    expression is well-typed when every operator that reads variables
    (FILTER, BIND, the conditions of DIFF and OPTIONAL) finds them at
    the representations required by Definition 5.43 ([env_meets], always
    at least ι), and PROJECTION only drops variables typed ι or ν.  The environment of the judgement is a lower bound on the
    representations of the result (see Typing.v, [env_ok]).

    [erase] forgets the promotions Υ of a condensed expression and gives
    the flat expression it computes.  The translation τ produces
    well-typed expressions whose erasure is the source expression
    ([translate_typed], [erase_translate]); Theorem 6.2 is proved for every
    well-typed condensed expression in Equivalence.v.
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
Require Import ConVerG.Translation.
Import ListNotations.

(** ** Side conditions *)

(** The variables typed by [env] that are not in [vars] are at least ι. *)
Definition env_dropped_ids (env : Environment) (vars : list Var) : Prop :=
  forall x r, env_lookup x env = Some r -> memb x vars = false -> Id <=_r r.

(** ** The typing judgement *)

Inductive typed : CondExpr -> Environment -> Prop :=
  | TyQuadPattern : forall s p o g,
      NoDup (quad_pat_vars s p o g) ->
      typed (QuadPatternC s p o g) (pat_env s p o g)
  | TyJoin : forall e1 e2 env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      typed (JoinC e1 e2) (env_meet env1 env2)
  | TyFilter : forall c e env,
      typed e env -> env_meets env (cond_reqs c) ->
      typed (FilterC c e) env
  | TyUnion : forall e1 e2 env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      typed (UnionC e1 e2) (env_meet env1 env2)
  | TyDiff : forall e1 e2 c env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      env_meets env1 (cond_reqs c) -> env_meets env2 (cond_reqs c) ->
      typed (DiffC e1 e2 c) env1
  | TyOptional : forall e1 e2 c env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      env_meets env1 (cond_reqs c) -> env_meets env2 (cond_reqs c) ->
      typed (OptionalC e1 e2 c) (env_meet env1 env2)
  | TyExtend : forall x ex e env,
      typed e env -> ~ In x (env_domain env) -> env_meets env (bind_reqs ex) ->
      typed (ExtendC x ex e) ((x, Value) :: env)
  | TyProjection : forall e vars env,
      typed e env -> env_dropped_ids env vars ->
      typed (ProjectionC e vars) (env_restrict env vars)
  | TyGroupAgg : forall ks aggs e env,
      typed e env ->
      env_meets env (map (fun x => (x, Id)) ks) ->
      Forall (fun ag => env_meets env (cond_reqs (agg_expr ag))) aggs ->
      NoDup ks -> NoDup (map agg_var aggs) ->
      (forall x, In x (map agg_var aggs) -> ~ In x ks) ->
      typed (GroupAggC ks aggs e) (groupagg_env env ks aggs)
  | TyTransformRepr : forall reqs e env,
      typed e env ->
      typed (TransformReprC reqs e) (env_raise env reqs)
  | TyGraphs : forall x,
      typed (GraphsC x) [(x, UnboundGraph)].

(** ** Erasure of the promotions *)

Fixpoint erase (ec : CondExpr) : FlatExpr :=
  match ec with
  | QuadPatternC s p o g => QuadPatternF s p o g
  | JoinC e1 e2 => JoinF (erase e1) (erase e2)
  | FilterC c e => FilterF c (erase e)
  | UnionC e1 e2 => UnionF (erase e1) (erase e2)
  | DiffC e1 e2 c => DiffF (erase e1) (erase e2) c
  | OptionalC e1 e2 c => OptionalF (erase e1) (erase e2) c
  | ExtendC x ex e => ExtendF x ex (erase e)
  | ProjectionC e vars => ProjectionF (erase e) vars
  | GroupAggC ks aggs e => GroupAggF ks aggs (erase e)
  | TransformReprC _ e => erase e
  | GraphsC x => GraphsF x
  end.

Lemma erase_translate : forall e, erase (fst (translate e)) = e.
Proof.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars
                  | ks aggs e IH | x].
  - rewrite translate_qp. reflexivity.
  - rewrite translate_join. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_filter. cbn [fst erase]. rewrite IH. reflexivity.
  - rewrite translate_union. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_diff. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_optional. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_extend. cbn [fst erase]. rewrite IH. reflexivity.
  - rewrite translate_projection. cbn [fst erase]. rewrite IH. reflexivity.
  - rewrite translate_groupagg. cbn [fst erase]. rewrite IH. reflexivity.
  - rewrite translate_graphs. reflexivity.
Qed.

(** ** The translation produces well-typed expressions *)

Lemma raise_needs_dropped : forall env vars,
  env_dropped_ids (env_raise env (needs env (dropped_vars env vars) Id)) vars.
Proof.
  intros env vars x r Hr Hx.
  assert (Hdom : In x (env_domain env)).
  { eapply (proj1 (raise_needs_domain _ _ _ _)). eapply env_lookup_in_domain; eauto. }
  apply (raise_needs_meets env (dropped_vars env vars) Id x r); [|exact Hr].
  unfold dropped_vars. apply filter_In. split; [exact Hdom | rewrite Hx; reflexivity].
Qed.

Theorem translate_typed : forall e,
  wf_flat_expr e -> typed (fst (translate e)) (snd (translate e)).
Proof.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars
                  | ks aggs e IH | x];
    intros Hwf; cbn [wf_flat_expr] in Hwf.
  - rewrite translate_qp. cbn [fst snd]. apply TyQuadPattern. exact Hwf.
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_join. cbn [fst snd].
    apply TyJoin; auto.
  - rewrite translate_filter. cbn [fst snd].
    apply TyFilter; [apply TyTransformRepr; auto | apply raise_needs_reqs_env_meets].
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_union. cbn [fst snd].
    apply TyUnion; auto.
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_diff. cbn [fst snd].
    apply TyDiff with (env2 := env_raise (snd (translate e2))
                                         (needs_reqs (snd (translate e2)) (cond_reqs c)));
      [apply TyTransformRepr; auto | apply TyTransformRepr; auto
      | apply raise_needs_reqs_env_meets | apply raise_needs_reqs_env_meets].
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_optional. cbn [fst snd].
    apply TyOptional;
      [apply TyTransformRepr; auto | apply TyTransformRepr; auto
      | apply raise_needs_reqs_env_meets | apply raise_needs_reqs_env_meets].
  - destruct Hwf as [Hx Hwf]. rewrite translate_extend. cbn [fst snd].
    apply TyExtend; [apply TyTransformRepr; auto | | apply raise_needs_reqs_env_meets].
    intros Hin. apply Hx. apply translate_domain.
    exact (proj1 (raise_needs_reqs_domain _ _ _) Hin).
  - rewrite translate_projection. cbn [fst snd].
    apply TyProjection; [apply TyTransformRepr; auto | apply raise_needs_dropped].
  - destruct Hwf as [Hks [Haggs [Hdisj Hwf]]]. rewrite translate_groupagg.
    cbn [fst snd].
    pose proof (raise_needs_reqs_env_meets (snd (translate e)) (groupagg_reqs ks aggs))
      as Hm.
    apply TyGroupAgg; try assumption.
    + apply TyTransformRepr. auto.
    + eapply env_meets_incl; [|exact Hm]. intros xr Hxr. unfold groupagg_reqs.
      apply in_app_iff. left. exact Hxr.
    + apply Forall_forall. intros ag Hag.
      eapply env_meets_incl; [|exact Hm]. intros xr Hxr. unfold groupagg_reqs.
      apply in_app_iff. right. apply in_flat_map. exists ag. auto.
  - rewrite translate_graphs. cbn [fst snd]. apply TyGraphs.
Qed.
