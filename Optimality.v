(** * Optimality: The Optimal Representation Function R-star

    Thesis, Section 5.4: expression typing (Definition 5.43), operator
    typing (Definition 5.44), lower environment (Definition 5.45), optimal
    representation function (Definition 5.46), Lemmas 5.2 and 5.3 and
    Theorem 5.1 (well-typedness of R-star).

    The thesis types a whole expression under a single environment Γ,
    which must satisfy the representation constraints of every operator
    of the expression: the judgement [Γ ⊢ e] ([tc]) is a *checking*
    judgement, and R-star(e) is defined as the greatest lower bound of all
    valid environments.  Here R-star is computed: [rstar e] is the pointwise
    least upper bound of the constraints of [e] ([constraints e]), and
    we prove that it is valid (Theorem 5.1), that it is below every valid
    environment, hence that it is the greatest lower bound of
    Definition 5.46.  This is the only sense in which R-star is "optimal"
    that does not depend on a cost model: it is the least informative
    environment under which every operator is well-typed.

    Two consequences are drawn for the translation τ (Translation.v):
    the environment rule of JOIN in the thesis is the pointwise *join*
    of the optimal environments of the operands ([rstar_join]), and τ
    only promotes a variable at an operator that requires it
    ([translate_lazy]).

    Corrections with respect to the thesis (see SPEC-extensions.md):
    Equality (Definition 5.43) requires both operands at least at ι
    (the rule as written requires the same representation on both
    sides); Extend requires its expression at ι as in the rule of
    Definition 5.44 (the text says ν); the constraints are those of the
    sub-tree, so that a variable introduced by BIND may be read above
    it; Projection requires the dropped variables at ι (bag semantics).
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
Require Import ConVerG.TypeSystem.
Import ListNotations.

(** ** Satisfaction of a list of constraints *)

(** Γ satisfies the constraints [reqs]: every constrained variable is in
    the domain of Γ, at least at the required representation. *)
Definition satisfies (env : Environment) (reqs : list (Var * Representation))
  : Prop :=
  forall x r, In (x, r) reqs ->
    exists r', env_lookup x env = Some r' /\ r <=_r r'.

Lemma satisfies_app : forall env l1 l2,
  satisfies env (l1 ++ l2) <-> satisfies env l1 /\ satisfies env l2.
Proof.
  intros env l1 l2. unfold satisfies. split.
  - intros H. split; intros x r Hx; apply H; apply in_app_iff; auto.
  - intros [H1 H2] x r Hx. apply in_app_iff in Hx. destruct Hx; auto.
Qed.

Lemma satisfies_flat_map : forall {A : Type} env (f : A -> list (Var * Representation)) l,
  satisfies env (flat_map f l) <-> Forall (fun a => satisfies env (f a)) l.
Proof.
  intros A env f l. rewrite Forall_forall. unfold satisfies. split.
  - intros H a Ha x r Hx. apply H. apply in_flat_map. eauto.
  - intros H x r Hx. apply in_flat_map in Hx. destruct Hx as [a [Ha Hx]].
    apply (H a Ha x r Hx).
Qed.

Lemma satisfies_mono : forall env1 env2 reqs,
  env1 <=_env env2 -> satisfies env1 reqs -> satisfies env2 reqs.
Proof.
  intros env1 env2 reqs Hle H x r Hx. destruct (H x r Hx) as [r1 [Hr1 Hle1]].
  destruct (Hle x r1 Hr1) as [r2 [Hr2 Hle2]]. exists r2.
  split; [exact Hr2 | eapply leq_repr_trans; eauto].
Qed.

(** ** Expression typing (Definition 5.43) *)

Inductive expr_ty (env : Environment) : SparqlExpr -> Representation -> Prop :=
  | ETTerm : forall t, expr_ty env (ExprTerm t) Value
  | ETVar : forall x r, env_lookup x env = Some r -> expr_ty env (ExprVar x) r
  | ETBound : forall x r,
      env_lookup x env = Some r -> Id <=_r r -> expr_ty env (ExprBound x) Value
  | ETEq : forall e1 e2 r1 r2,
      expr_ty env e1 r1 -> expr_ty env e2 r2 -> Id <=_r r1 -> Id <=_r r2 ->
      expr_ty env (ExprEq e1 e2) Value
  | ETFunc : forall n args,
      Forall (fun a => expr_ty env a Value) args ->
      expr_ty env (ExprFunc n args) Value.

Lemma expr_ty_term_inv : forall env t r, expr_ty env (ExprTerm t) r -> r = Value.
Proof. intros env t r H. inversion H. reflexivity. Qed.

Lemma expr_ty_var_inv : forall env x r,
  expr_ty env (ExprVar x) r -> env_lookup x env = Some r.
Proof. intros env x r H. inversion H. assumption. Qed.

Lemma expr_ty_bound_inv : forall env x r,
  expr_ty env (ExprBound x) r ->
  r = Value /\ exists r', env_lookup x env = Some r' /\ Id <=_r r'.
Proof.
  intros env x r H. inversion H; subst. split; [reflexivity|]. eexists. split; eassumption.
Qed.

Lemma expr_ty_eq_inv : forall env e1 e2 r,
  expr_ty env (ExprEq e1 e2) r ->
  r = Value /\
  (exists r1, expr_ty env e1 r1 /\ Id <=_r r1) /\
  (exists r2, expr_ty env e2 r2 /\ Id <=_r r2).
Proof.
  intros env e1 e2 r H. inversion H; subst. split; [reflexivity|].
  split; eexists; split; eassumption.
Qed.

Lemma expr_ty_func_inv : forall env n args r,
  expr_ty env (ExprFunc n args) r ->
  r = Value /\ Forall (fun a => expr_ty env a Value) args.
Proof. intros env n args r H. inversion H; subst. auto. Qed.

Lemma value_leq_eq : forall r, Value <=_r r -> r = Value.
Proof.
  intros r H. apply leq_repr_antisym; [apply value_greatest | exact H].
Qed.

(** The typing judgement of an expression is the satisfaction of its
    requirements ([expr_reqs_at], Expressions.v): the expression has a
    representation at least [r0] iff Γ satisfies [expr_reqs_at r0 e]. *)
Lemma expr_ty_reqs : forall env e r0,
  (exists r, expr_ty env e r /\ r0 <=_r r) <-> satisfies env (expr_reqs_at r0 e).
Proof.
  intros env e. induction e as [t | x | x | e1 e2 IH1 IH2 | n args IHargs]
    using SparqlExpr_ind'; intros r0; cbn [expr_reqs_at].
  - split.
    + intros _ x r [].
    + intros _. exists Value. split; [constructor | apply value_greatest].
  - split.
    + intros [r [H Hle]]. apply expr_ty_var_inv in H. intros y r' [Heq | []].
      injection Heq as <- <-. eauto.
    + intros H. destruct (H x r0 (or_introl eq_refl)) as [r [Hr Hle]].
      exists r. split; [constructor; exact Hr | exact Hle].
  - split.
    + intros [r [H _]]. apply expr_ty_bound_inv in H.
      destruct H as [_ [r' [Hr' Hle]]]. intros y r'' [Heq | []].
      injection Heq as <- <-. eauto.
    + intros H. destruct (H x Id (or_introl eq_refl)) as [r [Hr Hle]].
      exists Value. split; [econstructor; eauto | apply value_greatest].
  - rewrite satisfies_app, <- IH1, <- IH2. split.
    + intros [r [H _]]. apply expr_ty_eq_inv in H. tauto.
    + intros [[r1 [H1 Hle1]] [r2 [H2 Hle2]]]. exists Value.
      split; [econstructor; eauto | apply value_greatest].
  - rewrite satisfies_flat_map. split.
    + intros [r [H _]]. apply expr_ty_func_inv in H. destruct H as [_ H].
      rewrite Forall_forall in IHargs, H |- *. intros a Ha.
      apply (IHargs a Ha). exists Value. split; [apply H; exact Ha | apply leq_repr_refl].
    + intros H. exists Value. split; [|apply value_greatest]. constructor.
      rewrite Forall_forall in IHargs, H |- *. intros a Ha.
      destruct (proj2 (IHargs a Ha Value) (H a Ha)) as [r [Hr Hle]].
      rewrite (value_leq_eq r Hle) in Hr. exact Hr.
Qed.

Lemma expr_ty_cond : forall env c,
  expr_ty env c Value <-> satisfies env (cond_reqs c).
Proof.
  intros env c. unfold cond_reqs. rewrite <- expr_ty_reqs. split.
  - intros H. exists Value. split; [exact H | apply leq_repr_refl].
  - intros [r [H Hle]]. rewrite (value_leq_eq r Hle) in H. exact H.
Qed.

(** ** Operator typing (Definition 5.44): the constraints of an expression *)

(** The representation constraints imposed by the operators of [e]
    (lower bounds on the global environment). *)
Fixpoint constraints (e : FlatExpr) : list (Var * Representation) :=
  match e with
  | QuadPatternF s p o g =>
      map (fun x => (x, Id)) (pat_vars s ++ pat_vars p ++ pat_vars o)
      ++ map (fun x => (x, Condensed)) (pat_vars g)
  | JoinF e1 e2 => constraints e1 ++ constraints e2
  | FilterF c e => cond_reqs c ++ constraints e
  | UnionF e1 e2 => constraints e1 ++ constraints e2
  | DiffF e1 e2 c => cond_reqs c ++ constraints e1 ++ constraints e2
  | OptionalF e1 e2 c => cond_reqs c ++ constraints e1 ++ constraints e2
  | ExtendF x ex e => bind_reqs ex ++ constraints e
  | ProjectionF e vars =>
      map (fun x => (x, Id)) (filter (fun y => negb (memb y vars)) (flat_expr_vars e))
      ++ constraints e
  | GroupAggF ks aggs e => groupagg_reqs ks aggs ++ constraints e
  | GraphsF x => [(x, UnboundGraph)]
  end.

(** The checking judgement Γ ⊢ e of Definition 5.44. *)
Inductive tc (env : Environment) : FlatExpr -> Prop :=
  | TcQuadPattern : forall s p o g,
      satisfies env (map (fun x => (x, Id)) (pat_vars s ++ pat_vars p ++ pat_vars o)) ->
      satisfies env (map (fun x => (x, Condensed)) (pat_vars g)) ->
      tc env (QuadPatternF s p o g)
  | TcJoin : forall e1 e2, tc env e1 -> tc env e2 -> tc env (JoinF e1 e2)
  | TcFilter : forall c e, tc env e -> expr_ty env c Value -> tc env (FilterF c e)
  | TcUnion : forall e1 e2, tc env e1 -> tc env e2 -> tc env (UnionF e1 e2)
  | TcDiff : forall e1 e2 c,
      tc env e1 -> tc env e2 -> expr_ty env c Value -> tc env (DiffF e1 e2 c)
  | TcOptional : forall e1 e2 c,
      tc env e1 -> tc env e2 -> expr_ty env c Value -> tc env (OptionalF e1 e2 c)
  | TcExtend : forall x ex e r,
      tc env e -> expr_ty env ex r -> Id <=_r r -> tc env (ExtendF x ex e)
  | TcProjection : forall e vars,
      tc env e ->
      satisfies env (map (fun x => (x, Id))
                         (filter (fun y => negb (memb y vars)) (flat_expr_vars e))) ->
      tc env (ProjectionF e vars)
  | TcGroupAgg : forall ks aggs e,
      tc env e ->
      satisfies env (map (fun x => (x, Id)) ks) ->
      Forall (fun ag => expr_ty env (agg_expr ag) Value) aggs ->
      tc env (GroupAggF ks aggs e)
  | TcGraphs : forall x,
      satisfies env [(x, UnboundGraph)] -> tc env (GraphsF x).

(** Γ ⊢ e holds exactly when Γ satisfies the constraints of [e]. *)
Theorem tc_iff : forall env e, tc env e <-> satisfies env (constraints e).
Proof.
  intros env e.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars
                  | ks aggs e IH | x]; cbn [constraints].
  - split.
    + intros H. inversion H; subst. apply satisfies_app. auto.
    + intros H. apply satisfies_app in H. constructor; tauto.
  - rewrite satisfies_app, <- IH1, <- IH2. split.
    + intros H. inversion H; subst. auto.
    + intros [H1 H2]. constructor; assumption.
  - rewrite satisfies_app, <- IH, <- expr_ty_cond. split.
    + intros H. inversion H; subst. auto.
    + intros [H1 H2]. constructor; assumption.
  - rewrite satisfies_app, <- IH1, <- IH2. split.
    + intros H. inversion H; subst. auto.
    + intros [H1 H2]. constructor; assumption.
  - rewrite !satisfies_app, <- IH1, <- IH2, <- expr_ty_cond. split.
    + intros H. inversion H; subst. auto.
    + intros [H [H1 H2]]. constructor; assumption.
  - rewrite !satisfies_app, <- IH1, <- IH2, <- expr_ty_cond. split.
    + intros H. inversion H; subst. auto.
    + intros [H [H1 H2]]. constructor; assumption.
  - rewrite satisfies_app, <- IH. unfold bind_reqs. rewrite <- expr_ty_reqs. split.
    + intros H. inversion H; subst. eauto.
    + intros [[r [Hr Hle]] H]. econstructor; eauto.
  - rewrite satisfies_app, <- IH. split.
    + intros H. inversion H; subst. auto.
    + intros [H1 H2]. constructor; assumption.
  - unfold groupagg_reqs. rewrite !satisfies_app, <- IH, satisfies_flat_map. split.
    + intros H. inversion H; subst. split; [split; [assumption|]|assumption].
      eapply Forall_impl; [|eassumption]. intros ag. apply expr_ty_cond.
    + intros [[H1 H2] H3]. constructor; [assumption | assumption|].
      eapply Forall_impl; [|exact H2]. intros ag. apply expr_ty_cond.
  - split.
    + intros H. inversion H; subst. assumption.
    + intros H. constructor. exact H.
Qed.

(** ** Lower environment (Definition 5.45) and Lemmas 5.2, 5.3 *)

(** Γ1 ⊓ Γ2 on the common domain. *)
Definition env_glb (env1 env2 : Environment) : Environment :=
  filter_map (fun xr : Var * Representation =>
                match env_lookup (fst xr) env2 with
                | Some r2 => Some (fst xr, snd xr ⊓ r2)
                | None => None
                end) env1.

Lemma env_glb_lookup : forall env1 env2 x,
  env_lookup x (env_glb env1 env2) =
  match env_lookup x env1, env_lookup x env2 with
  | Some r1, Some r2 => Some (r1 ⊓ r2)
  | _, _ => None
  end.
Proof.
  intros env1 env2 x. induction env1 as [|[y r1] env1 IH]; [reflexivity|].
  unfold env_glb, filter_map in *. cbn [flat_map fst snd].
  destruct (Var_eq_dec x y) as [-> | Hneq].
  - cbn [env_lookup]. destruct (Var_eq_dec y y) as [_ | Hc]; [|contradiction].
    destruct (env_lookup y env2) as [r2|] eqn:E2.
    + cbn [app env_lookup]. destruct (Var_eq_dec y y); [reflexivity | contradiction].
    + cbn [app]. rewrite IH. destruct (env_lookup y env1); reflexivity.
  - cbn [env_lookup]. destruct (Var_eq_dec x y) as [Hc | _]; [contradiction|].
    destruct (env_lookup y env2) as [r2|] eqn:E2.
    + cbn [app env_lookup]. destruct (Var_eq_dec x y); [contradiction | exact IH].
    + cbn [app]. exact IH.
Qed.

Lemma meet_repr_idem : forall r, r ⊓ r = r.
Proof. intros r. unfold meet_repr. destruct (leq_repr_dec r r); reflexivity. Qed.

(** Lemma 5.2 (Expression Typing Intersection). *)
Lemma expr_ty_glb : forall env1 env2 e r1 r2,
  expr_ty env1 e r1 -> expr_ty env2 e r2 ->
  expr_ty (env_glb env1 env2) e (r1 ⊓ r2).
Proof.
  intros env1 env2 e. induction e as [t | x | x | e1 e2 IH1 IH2 | n args IHargs]
    using SparqlExpr_ind'; intros r1 r2 H1 H2.
  - apply expr_ty_term_inv in H1. apply expr_ty_term_inv in H2. subst.
    rewrite meet_repr_idem. constructor.
  - apply expr_ty_var_inv in H1. apply expr_ty_var_inv in H2.
    constructor. rewrite env_glb_lookup, H1, H2. reflexivity.
  - apply expr_ty_bound_inv in H1. apply expr_ty_bound_inv in H2.
    destruct H1 as [-> [r1' [Hr1 Hle1]]]. destruct H2 as [-> [r2' [Hr2 Hle2]]].
    rewrite meet_repr_idem. apply (ETBound _ x (r1' ⊓ r2')).
    + rewrite env_glb_lookup, Hr1, Hr2. reflexivity.
    + apply meet_repr_glb; assumption.
  - apply expr_ty_eq_inv in H1. apply expr_ty_eq_inv in H2.
    destruct H1 as [-> [[r11 [H11 L11]] [r12 [H12 L12]]]].
    destruct H2 as [-> [[r21 [H21 L21]] [r22 [H22 L22]]]].
    rewrite meet_repr_idem.
    apply (ETEq _ e1 e2 (r11 ⊓ r21) (r12 ⊓ r22)); auto; apply meet_repr_glb; assumption.
  - apply expr_ty_func_inv in H1. apply expr_ty_func_inv in H2.
    destruct H1 as [-> H1]. destruct H2 as [-> H2]. rewrite meet_repr_idem.
    constructor. rewrite Forall_forall in IHargs, H1, H2 |- *. intros a Ha.
    rewrite <- (meet_repr_idem Value). apply IHargs; auto.
Qed.

Lemma satisfies_glb : forall env1 env2 reqs,
  satisfies env1 reqs -> satisfies env2 reqs -> satisfies (env_glb env1 env2) reqs.
Proof.
  intros env1 env2 reqs H1 H2 x r Hx.
  destruct (H1 x r Hx) as [r1 [Hr1 Hle1]]. destruct (H2 x r Hx) as [r2 [Hr2 Hle2]].
  exists (r1 ⊓ r2). rewrite env_glb_lookup, Hr1, Hr2. split; [reflexivity|].
  apply meet_repr_glb; assumption.
Qed.

(** Lemma 5.3 (Operator Typing Intersection). *)
Theorem tc_glb : forall env1 env2 e,
  tc env1 e -> tc env2 e -> tc (env_glb env1 env2) e.
Proof.
  intros env1 env2 e H1 H2. apply tc_iff. apply satisfies_glb; apply tc_iff; assumption.
Qed.

(** ** The optimal representation function (Definition 5.46) *)

(** R-star(e): the pointwise least upper bound of the constraints of [e]. *)
Definition rstar (e : FlatExpr) : Environment := env_raise [] (constraints e).

(** Raising from the empty environment gives the least environment
    satisfying the constraints. *)
Lemma env_raise_nil_satisfies : forall reqs, satisfies (env_raise [] reqs) reqs.
Proof.
  intros reqs x r Hx. apply env_raise_meets. exact Hx.
Qed.

Lemma env_raise_lub : forall env reqs env',
  env <=_env env' -> satisfies env' reqs -> env_raise env reqs <=_env env'.
Proof.
  intros env reqs env' Hle Hsat x r Hr.
  assert (Hdom : In x (env_domain (env_raise env reqs)))
    by (eapply env_lookup_in_domain; eauto).
  apply env_raise_domain in Hdom.
  assert (Hx : exists r', env_lookup x env' = Some r').
  { destruct Hdom as [Hdom | Hdom].
    - apply in_map_iff in Hdom. destruct Hdom as [[y r0] [<- Hy]]. cbn [fst].
      destruct (Hsat y r0 Hy) as [r' [Hr' _]]. eauto.
    - destruct (env_domain_lookup x env Hdom) as [r0 Hr0].
      destruct (Hle x r0 Hr0) as [r' [Hr' _]]. eauto. }
  destruct Hx as [r' Hr']. exists r'. split; [exact Hr'|].
  eapply env_raise_lookup_lub; [exact Hr | |].
  - intros r0 Hr0. destruct (Hle x r0 Hr0) as [r'' [Hr'' Hle'']].
    rewrite Hr' in Hr''. injection Hr'' as <-. exact Hle''.
  - intros r0 Hr0. destruct (Hsat x r0 Hr0) as [r'' [Hr'' Hle'']].
    rewrite Hr' in Hr''. injection Hr'' as <-. exact Hle''.
Qed.

Lemma env_leq_nil : forall env, [] <=_env env.
Proof. intros env x r H. discriminate H. Qed.

Lemma env_raise_nil_least : forall reqs env,
  satisfies env reqs -> env_raise [] reqs <=_env env.
Proof.
  intros reqs env H. apply env_raise_lub; [apply env_leq_nil | exact H].
Qed.

(** Theorem 5.1 (Well-Typedness of the Optimal Representation). *)
Theorem rstar_well_typed : forall e, tc (rstar e) e.
Proof. intros e. apply tc_iff. apply env_raise_nil_satisfies. Qed.

(** R-star(e) is below every valid environment ... *)
Theorem rstar_least : forall e env, tc env e -> rstar e <=_env env.
Proof.
  intros e env H. apply env_raise_nil_least. apply tc_iff. exact H.
Qed.

(** ... hence it is the greatest lower bound of the valid environments
    (Definition 5.46), unique up to the equivalence of environments. *)
Definition env_equiv (env1 env2 : Environment) : Prop :=
  env1 <=_env env2 /\ env2 <=_env env1.

Theorem rstar_glb : forall e env0,
  tc env0 e ->
  (forall env, tc env e -> env0 <=_env env) ->
  env_equiv env0 (rstar e).
Proof.
  intros e env0 H0 Hleast. split.
  - apply Hleast. apply rstar_well_typed.
  - apply rstar_least. exact H0.
Qed.

(** R-star(e) has no duplicate variable, so membership and lookup agree. *)
Lemma env_raise_var_NoDup : forall x r env,
  NoDup (env_domain env) -> NoDup (env_domain (env_raise_var x r env)).
Proof.
  intros x r env. induction env as [|[y r'] env IH]; simpl; intros H.
  - repeat constructor. intros [].
  - apply NoDup_cons_iff in H. destruct H as [Hnotin Hnd].
    destruct (Var_eq_dec x y) as [-> | Hneq]; simpl.
    + constructor; assumption.
    + constructor; [|apply IH; exact Hnd].
      intros Hy. apply (env_raise_var_domain x r env y) in Hy.
      destruct Hy as [-> | Hy]; [apply Hneq; reflexivity | exact (Hnotin Hy)].
Qed.

Lemma env_raise_NoDup : forall env reqs,
  NoDup (env_domain env) -> NoDup (env_domain (env_raise env reqs)).
Proof.
  intros env reqs H. induction reqs as [|[x r] reqs IH]; simpl; [exact H|].
  apply env_raise_var_NoDup. exact IH.
Qed.

Lemma rstar_NoDup : forall e, NoDup (env_domain (rstar e)).
Proof. intros e. apply env_raise_NoDup. constructor. Qed.

Lemma env_leq_satisfies : forall env1 env2,
  NoDup (env_domain env1) ->
  (env1 <=_env env2 <-> satisfies env2 env1).
Proof.
  intros env1 env2 Hnd. split.
  - intros Hle x r Hx. apply Hle. rewrite env_lookup_eq.
    apply in_lookup_NoDup; [exact Hnd | exact Hx].
  - intros Hsat x r Hx. apply Hsat. rewrite env_lookup_eq in Hx.
    apply lookup_Some_In. exact Hx.
Qed.

(** ** The environment rule of JOIN *)

(** Under the rule of Definition 5.44, both operands of a join are typed
    under the same environment ... *)
Lemma tc_join : forall env e1 e2,
  tc env (JoinF e1 e2) <-> tc env e1 /\ tc env e2.
Proof.
  intros env e1 e2. split.
  - intros H. inversion H; subst. auto.
  - intros [H1 H2]. constructor; assumption.
Qed.

(** ... so the optimal environment of a join is the pointwise *join* of
    the optimal environments of its operands (Example 5.17): a shared
    variable is promoted, before ⋈_C, to the higher of the two
    representations.  The translation [translate] does not promote
    before ⋈_C (its merge is semantic) and therefore guarantees only the
    pointwise meet of the environments of the operands; both rules are
    sound, see [typed_correct] (Equivalence.v). *)
Theorem rstar_join : forall e1 e2,
  env_equiv (rstar (JoinF e1 e2)) (env_join (rstar e1) (rstar e2)).
Proof.
  intros e1 e2. unfold env_join.
  pose proof (env_raise_nil_satisfies (constraints e1)) as S1.
  pose proof (env_raise_nil_satisfies (constraints e2)) as S2.
  assert (Hle1 : rstar e1 <=_env env_raise (rstar e1) (rstar e2))
    by apply env_raise_geq.
  assert (Hle2 : rstar e2 <=_env env_raise (rstar e1) (rstar e2)).
  { apply env_leq_satisfies; [apply rstar_NoDup|].
    intros x r Hx. apply env_raise_meets. exact Hx. }
  split.
  - (* R-star(join) ≤ R-star(e1) ⊔ R-star(e2) *)
    apply env_raise_nil_least. cbn [constraints]. apply satisfies_app. split.
    + eapply satisfies_mono; [exact Hle1 | exact S1].
    + eapply satisfies_mono; [exact Hle2 | exact S2].
  - (* R-star(e1) ⊔ R-star(e2) ≤ R-star(join) *)
    assert (Hj : satisfies (rstar (JoinF e1 e2)) (constraints e1 ++ constraints e2))
      by apply env_raise_nil_satisfies.
    apply satisfies_app in Hj. destruct Hj as [J1 J2].
    apply env_raise_lub.
    + apply env_raise_nil_least. exact J1.
    + apply env_leq_satisfies; [apply rstar_NoDup|].
      apply env_raise_nil_least. exact J2.
Qed.

(** ** The translation τ promotes only on demand *)

(** A promotion Υ_reqs is justified by the operator directly above it
    when every requirement of [reqs] is a requirement of that operator
    (Definition 5.47 inserts Υ(R-star(e_i), R-star(e)) exactly there). *)
Definition promo_ok (lazy : CondExpr -> Prop)
  (allowed : Var * Representation -> Prop) (ec : CondExpr) : Prop :=
  match ec with
  | TransformReprC reqs e => (forall xr, In xr reqs -> allowed xr) /\ lazy e
  | _ => lazy ec
  end.

Fixpoint lazy (ec : CondExpr) : Prop :=
  match ec with
  | QuadPatternC _ _ _ _ => True
  | GraphsC _ => True
  | JoinC e1 e2 => lazy e1 /\ lazy e2
  | UnionC e1 e2 => lazy e1 /\ lazy e2
  | FilterC c e => promo_ok lazy (fun xr => In xr (cond_reqs c)) e
  | DiffC e1 e2 c =>
      promo_ok lazy (fun xr => In xr (cond_reqs c)) e1 /\
      promo_ok lazy (fun xr => In xr (cond_reqs c)) e2
  | OptionalC e1 e2 c =>
      promo_ok lazy (fun xr => In xr (cond_reqs c)) e1 /\
      promo_ok lazy (fun xr => In xr (cond_reqs c)) e2
  | ExtendC _ ex e => promo_ok lazy (fun xr => In xr (bind_reqs ex)) e
  | ProjectionC e vars =>
      promo_ok lazy (fun xr => snd xr = Id /\ memb (fst xr) vars = false) e
  | GroupAggC ks aggs e => promo_ok lazy (fun xr => In xr (groupagg_reqs ks aggs)) e
  | TransformReprC _ _ => False
  end.

Lemma needs_reqs_incl : forall env reqs xr,
  In xr (needs_reqs env reqs) -> In xr reqs.
Proof.
  intros env reqs xr H. unfold needs_reqs in H. apply filter_In in H. tauto.
Qed.

Theorem translate_lazy : forall e, lazy (translate_expr e).
Proof.
  intros e. unfold translate_expr.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars
                  | ks aggs e IH | x].
  - rewrite translate_qp. exact I.
  - rewrite translate_join. cbn [fst lazy]. auto.
  - rewrite translate_filter. cbn [fst lazy promo_ok]. split; [|exact IH].
    intros xr Hxr. eapply needs_reqs_incl. exact Hxr.
  - rewrite translate_union. cbn [fst lazy]. auto.
  - rewrite translate_diff. cbn [fst lazy promo_ok]. split; split;
      try assumption; intros xr Hxr; eapply needs_reqs_incl; exact Hxr.
  - rewrite translate_optional. cbn [fst lazy promo_ok]. split; split;
      try assumption; intros xr Hxr; eapply needs_reqs_incl; exact Hxr.
  - rewrite translate_extend. cbn [fst lazy promo_ok]. split; [|exact IH].
    intros xr Hxr. eapply needs_reqs_incl. exact Hxr.
  - rewrite translate_projection. cbn [fst lazy promo_ok]. split; [|exact IH].
    intros [y r] Hxr. apply needs_reqs_incl in Hxr. apply in_map_iff in Hxr.
    destruct Hxr as [z [Heq Hz]]. injection Heq as <- <-. cbn [fst snd].
    split; [reflexivity|]. unfold dropped_vars in Hz. apply filter_In in Hz.
    destruct Hz as [_ Hz]. apply negb_true_iff in Hz. exact Hz.
  - rewrite translate_groupagg. cbn [fst lazy promo_ok]. split; [|exact IH].
    intros xr Hxr. eapply needs_reqs_incl. exact Hxr.
  - rewrite translate_graphs. exact I.
Qed.
