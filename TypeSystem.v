(** * TypeSystem: Typing of Condensed Expressions

    Thesis, Definition 5.38 (type system Γ ⊢ E_C ⇒ Γ').  A condensed
    expression is well-typed when every operator that needs point-valued
    variables (FILTER, BIND, the conditions of DIFF and OPTIONAL) only
    reads variables typed ι or ν, and PROJECTION only drops variables typed
    ι or ν.  The environment of the judgement is a lower bound on the
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
Require Import ConVerG.Typing.
Require Import ConVerG.FlatAlgebra.
Require Import ConVerG.CondensedAlgebra.
Require Import ConVerG.Translation.
Import ListNotations.

(** ** Side conditions *)

(** The variables of [xs] that are typed by [env] are point-valued. *)
Definition env_points (env : Environment) (xs : list Var) : Prop :=
  forall x r, In x xs -> env_lookup x env = Some r -> point_repr r = true.

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
      typed e env -> env_points env (expr_vars c) ->
      typed (FilterC c e) env
  | TyUnion : forall e1 e2 env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      typed (UnionC e1 e2) (env_meet env1 env2)
  | TyDiff : forall e1 e2 c env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      env_points env1 (expr_vars c) -> env_points env2 (expr_vars c) ->
      typed (DiffC e1 e2 c) env1
  | TyOptional : forall e1 e2 c env1 env2,
      typed e1 env1 -> typed e2 env2 ->
      env_points env1 (expr_vars c) -> env_points env2 (expr_vars c) ->
      typed (OptionalC e1 e2 c) (env_meet env1 env2)
  | TyExtend : forall x ex e env,
      typed e env -> ~ In x (env_domain env) -> env_points env (expr_vars ex) ->
      typed (ExtendC x ex e) ((x, Value) :: env)
  | TyProjection : forall e vars env,
      typed e env -> env_dropped_ids env vars ->
      typed (ProjectionC e vars) (env_restrict env vars)
  | TyTransformRepr : forall reqs e env,
      typed e env ->
      typed (TransformReprC reqs e) (env_raise env reqs).

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
  | TransformReprC _ e => erase e
  end.

Lemma erase_translate : forall e, erase (fst (translate e)) = e.
Proof.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars].
  - rewrite translate_qp. reflexivity.
  - rewrite translate_join. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_filter. cbn [fst erase]. rewrite IH. reflexivity.
  - rewrite translate_union. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_diff. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_optional. cbn [fst erase]. rewrite IH1, IH2. reflexivity.
  - rewrite translate_extend. cbn [fst erase]. rewrite IH. reflexivity.
  - rewrite translate_projection. cbn [fst erase]. rewrite IH. reflexivity.
Qed.

(** ** The translation produces well-typed expressions *)

Lemma raise_needs_points : forall env xs,
  env_points (env_raise env (needs env xs Value)) xs.
Proof.
  intros env xs x r Hx Hr.
  pose proof (raise_needs_meets env xs Value x r Hx Hr) as H.
  eapply point_repr_mono; [exact H | reflexivity].
Qed.

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
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars];
    intros Hwf; cbn [wf_flat_expr] in Hwf.
  - rewrite translate_qp. cbn [fst snd]. apply TyQuadPattern. exact Hwf.
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_join. cbn [fst snd].
    apply TyJoin; auto.
  - rewrite translate_filter. cbn [fst snd].
    apply TyFilter; [apply TyTransformRepr; auto | apply raise_needs_points].
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_union. cbn [fst snd].
    apply TyUnion; auto.
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_diff. cbn [fst snd].
    apply TyDiff with (env2 := env_raise (snd (translate e2))
                                         (needs (snd (translate e2)) (expr_vars c) Value));
      [apply TyTransformRepr; auto | apply TyTransformRepr; auto
      | apply raise_needs_points | apply raise_needs_points].
  - destruct Hwf as [Hwf1 Hwf2]. rewrite translate_optional. cbn [fst snd].
    apply TyOptional;
      [apply TyTransformRepr; auto | apply TyTransformRepr; auto
      | apply raise_needs_points | apply raise_needs_points].
  - destruct Hwf as [Hx Hwf]. rewrite translate_extend. cbn [fst snd].
    apply TyExtend; [apply TyTransformRepr; auto | | apply raise_needs_points].
    intros Hin. apply Hx. apply translate_domain.
    exact (proj1 (raise_needs_domain _ _ _ _) Hin).
  - rewrite translate_projection. cbn [fst snd].
    apply TyProjection; [apply TyTransformRepr; auto | apply raise_needs_dropped].
Qed.
