(** * Typing: Environments as Invariants of Condensed Evaluation

    Thesis, Section 5.4 (type system, Definition 5.38) and Section 5.5
    (optimal representation function R-star).

    An environment Γ is used here as a lower bound on the representations
    of the bindings of a condensed mapping ([env_ok]): every bound
    variable belongs to the domain of Γ and its binding has a
    representation at least Γ(x).  The translation τ (Translation.v)
    inserts a promotion Υ whenever an operator needs a point-valued
    variable; [env_ok] then guarantees that the variable is point-valued
    in every mapping, which is what Lemma 6.3 needs.
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Require Import ConVerG.Promotion.
Require Import ConVerG.Difference.
Import ListNotations.

(** ** Environments as association lists *)

Lemma env_lookup_eq : forall x (env : Environment),
  env_lookup x env = lookup x env.
Proof.
  intros x env. induction env as [|[y r] env IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec x y); [reflexivity | exact IH].
Qed.

Lemma env_domain_eq : forall (env : Environment), env_domain env = keys env.
Proof. reflexivity. Qed.

(** ** The invariant *)

Definition env_ok (env : Environment) (m : CMapping) : Prop :=
  forall x b, lookup x m = Some b ->
    exists r, env_lookup x env = Some r /\ r <=_r binding_repr b.

Lemma env_ok_point_on : forall env m xs,
  env_ok env m ->
  (forall x r, In x xs -> env_lookup x env = Some r -> point_repr r = true) ->
  point_on xs m.
Proof.
  intros env m xs Hok Hp x b Hx Hl. destruct (Hok x b Hl) as [r [Hr Hle]].
  apply point_val_repr. eapply point_repr_mono; [exact Hle | apply (Hp x r Hx Hr)].
Qed.

Lemma env_ok_keys_domain : forall env m x,
  env_ok env m -> In x (keys m) -> In x (env_domain env).
Proof.
  intros env m x Hok Hx. destruct (In_keys_lookup x m Hx) as [b Hb].
  destruct (Hok x b Hb) as [r [Hr _]]. eapply env_lookup_in_domain; eauto.
Qed.

(** Γ' is weaker than Γ: it is defined wherever Γ is, with a lower
    representation. *)
Definition env_weaker (env' env : Environment) : Prop :=
  forall x r, env_lookup x env = Some r ->
    exists r', env_lookup x env' = Some r' /\ r' <=_r r.

Lemma env_ok_weaken : forall env env' m,
  env_weaker env' env -> env_ok env m -> env_ok env' m.
Proof.
  intros env env' m Hw Hok x b Hl. destruct (Hok x b Hl) as [r [Hr Hle]].
  destruct (Hw x r Hr) as [r' [Hr' Hle']]. exists r'.
  split; [exact Hr' | eapply leq_repr_trans; eauto].
Qed.

(** ** Pointwise meet of environments *)

(** Γ1 ⊓ Γ2: the meet on shared variables, the union of the domains.
    This is the environment of a join or a union: a variable bound on
    both sides has, after merging, a representation at least the meet of
    the two; a variable bound on one side only keeps its representation.
    (The pointwise join ⊔ would be unsound for a variable that may be
    unbound on one side, e.g. after UNION or OPTIONAL.) *)
Definition env_meet (env1 env2 : Environment) : Environment :=
  map (fun xr =>
         (fst xr, match env_lookup (fst xr) env2 with
                  | Some r2 => snd xr ⊓ r2
                  | None => snd xr
                  end)) env1
  ++ filter (fun xr => negb (in_env_domain (fst xr) env1)) env2.

Lemma env_meet_lookup : forall env1 env2 x,
  env_lookup x (env_meet env1 env2) =
  match env_lookup x env1 with
  | Some r1 => Some (match env_lookup x env2 with
                     | Some r2 => r1 ⊓ r2
                     | None => r1
                     end)
  | None => env_lookup x env2
  end.
Proof.
  intros env1 env2 x. unfold env_meet. rewrite !env_lookup_eq.
  rewrite lookup_app, lookup_map_fst.
  destruct (lookup x env1) as [r1|] eqn:E1.
  - cbn [fst snd]. rewrite env_lookup_eq. reflexivity.
  - apply lookup_filter_keep. intros r. cbn [fst]. apply negb_true_iff.
    unfold in_env_domain. apply inb_false_iff. apply lookup_None_iff. exact E1.
Qed.

Lemma env_meet_weaker_l : forall env1 env2, env_weaker (env_meet env1 env2) env1.
Proof.
  intros env1 env2 x r Hr. rewrite env_meet_lookup, Hr.
  destruct (env_lookup x env2) as [r2|].
  - exists (r ⊓ r2). split; [reflexivity | apply meet_repr_lb_l].
  - exists r. split; [reflexivity | apply leq_repr_refl].
Qed.

Lemma env_meet_weaker_r : forall env1 env2, env_weaker (env_meet env1 env2) env2.
Proof.
  intros env1 env2 x r Hr. rewrite env_meet_lookup.
  destruct (env_lookup x env1) as [r1|].
  - rewrite Hr. exists (r1 ⊓ r). split; [reflexivity | apply meet_repr_lb_r].
  - exists r. split; [exact Hr | apply leq_repr_refl].
Qed.

Lemma env_meet_domain : forall env1 env2 x,
  In x (env_domain (env_meet env1 env2)) ->
  In x (env_domain env1) \/ In x (env_domain env2).
Proof.
  intros env1 env2 x Hx. destruct (env_domain_lookup x _ Hx) as [r Hr].
  rewrite env_meet_lookup in Hr.
  destruct (env_lookup x env1) as [r1|] eqn:E1.
  - left. eapply env_lookup_in_domain; eauto.
  - right. eapply env_lookup_in_domain; eauto.
Qed.

Lemma meet_repr_mono : forall r1 r1' r2 r2',
  r1 <=_r r1' -> r2 <=_r r2' -> r1 ⊓ r2 <=_r r1' ⊓ r2'.
Proof.
  intros r1 r1' r2 r2' H1 H2. apply meet_repr_glb.
  - eapply leq_repr_trans; [apply meet_repr_lb_l | exact H1].
  - eapply leq_repr_trans; [apply meet_repr_lb_r | exact H2].
Qed.

(** Merging two bindings does not go below the meet of their
    representations. *)
Lemma merge_binding_repr : forall b1 b2 b,
  merge_binding b1 b2 = Some b ->
  binding_repr b1 ⊓ binding_repr b2 <=_r binding_repr b.
Proof.
  intros b1 b2 b H. unfold merge_binding in H.
  destruct (point_val b1) as [t1|] eqn:E1.
  - destruct (in_dec Term_eq_dec t1 (vals b2)); [|discriminate].
    injection H as <-. apply meet_repr_lb_l.
  - destruct (point_val b2) as [t2|] eqn:E2.
    + destruct (in_dec Term_eq_dec t2 (vals b1)); [|discriminate].
      injection H as <-. apply meet_repr_lb_r.
    + destruct b1 as [| | g1 vs1 | cat1]; try discriminate;
        destruct b2 as [| | g2 vs2 | cat2]; try discriminate.
      * destruct (IRI_eq_dec g1 g2); [|discriminate].
        destruct (version_set_intersection vs1 vs2); [discriminate|].
        injection H as <-. apply meet_repr_lb_l.
      * destruct (filter _ vs1); [discriminate|]. injection H as <-.
        apply meet_repr_lb_l.
      * destruct (flat_map _ _); [discriminate|]. injection H as <-.
        apply meet_repr_lb_r.
      * destruct (cat_restrict _ _); [discriminate|]. injection H as <-.
        apply meet_repr_lb_l.
Qed.

(** The invariant for a condensed merge. *)
Lemma env_ok_merge_cond : forall env1 env2 m1 m2,
  env_ok env1 m1 -> env_ok env2 m2 -> compat_cond m1 m2 = true ->
  env_ok (env_meet env1 env2) (merge_cond m1 m2).
Proof.
  intros env1 env2 m1 m2 H1 H2 Hcc x b Hl.
  rewrite lookup_merge_cond in Hl. rewrite env_meet_lookup.
  rewrite compat_cond_iff in Hcc.
  destruct (lookup x m1) as [b1|] eqn:E1.
  - injection Hl as <-. destruct (H1 x b1 E1) as [r1 [Hr1 Hle1]]. rewrite Hr1.
    unfold merge_entry. cbn [fst snd].
    destruct (lookup x m2) as [b2|] eqn:E2.
    + destruct (H2 x b2 E2) as [r2 [Hr2 Hle2]]. rewrite Hr2.
      destruct (Hcc x b1 b2 (lookup_Some_In _ _ _ E1) E2) as [b Hb]. rewrite Hb.
      eexists. split; [reflexivity|].
      eapply leq_repr_trans; [apply meet_repr_mono; eauto | apply merge_binding_repr; exact Hb].
    + destruct (env_lookup x env2) as [r2|].
      * eexists. split; [reflexivity|].
        eapply leq_repr_trans; [apply meet_repr_lb_l | exact Hle1].
      * eexists. split; [reflexivity | exact Hle1].
  - destruct (H2 x b Hl) as [r2 [Hr2 Hle2]].
    destruct (env_lookup x env1) as [r1|].
    + rewrite Hr2. eexists. split; [reflexivity|].
      eapply leq_repr_trans; [apply meet_repr_lb_r | exact Hle2].
    + exists r2. split; [exact Hr2 | exact Hle2].
Qed.

(** ** Raising an environment *)

Lemma env_raise_lookup_lub : forall env reqs x r' rho,
  env_lookup x (env_raise env reqs) = Some r' ->
  (forall r0, env_lookup x env = Some r0 -> r0 <=_r rho) ->
  (forall r, In (x, r) reqs -> r <=_r rho) ->
  r' <=_r rho.
Proof.
  intros env reqs x. induction reqs as [|[y r0] reqs IH]; simpl;
    intros r' rho Hl Henv Hreqs.
  - apply Henv. exact Hl.
  - destruct (Var_eq_dec y x) as [-> | Hneq].
    + rewrite env_raise_var_lookup_same in Hl. injection Hl as <-.
      destruct (env_lookup x (env_raise env reqs)) as [r''|] eqn:E.
      * apply join_repr_lub.
        -- apply (IH r'' rho eq_refl Henv). intros r Hr. apply Hreqs. right. exact Hr.
        -- apply Hreqs. left. reflexivity.
      * apply Hreqs. left. reflexivity.
    + rewrite env_raise_var_lookup_other in Hl by exact Hneq.
      apply (IH r' rho Hl Henv). intros r Hr. apply Hreqs. right. exact Hr.
Qed.

(** The invariant after a promotion. *)
Lemma env_ok_promote : forall env reqs m m',
  env_ok env m -> In m' (promote reqs m) -> env_ok (env_raise env reqs) m'.
Proof.
  intros env reqs m m' Hok Hm' x b' Hl.
  destruct (promote_lookup reqs m m' x b' Hm' Hl) as [b [Hb [Hle [Hreqs _]]]].
  destruct (Hok x b Hb) as [r [Hr Hrle]].
  assert (Hdom : In x (env_domain (env_raise env reqs))).
  { apply env_raise_domain. right. eapply env_lookup_in_domain; eauto. }
  destruct (env_domain_lookup x _ Hdom) as [r' Hr'].
  exists r'. split; [exact Hr'|].
  eapply env_raise_lookup_lub; [exact Hr' | | exact Hreqs].
  intros r0 Hr0. rewrite Hr in Hr0. injection Hr0 as <-.
  eapply leq_repr_trans; eauto.
Qed.

(** ** Requirements *)

(** The requirements of [reqs] on the variables that are in the domain
    of Γ (a variable outside the domain is never bound, see
    [env_ok_keys_domain], so it needs no promotion). *)
Definition needs_reqs (env : Environment) (reqs : list (Var * Representation))
  : list (Var * Representation) :=
  filter (fun xr => in_env_domain (fst xr) env) reqs.

(** The requirements raising the variables of [xs] to representation
    [r]. *)
Definition needs (env : Environment) (xs : list Var) (r : Representation)
  : list (Var * Representation) :=
  needs_reqs env (map (fun x => (x, r)) xs).

Lemma needs_reqs_keys : forall env reqs x,
  In x (map fst (needs_reqs env reqs)) -> In x (env_domain env).
Proof.
  intros env reqs x Hx. unfold needs_reqs in Hx.
  apply in_map_iff in Hx. destruct Hx as [[y r] [<- Hy]]. apply filter_In in Hy.
  destruct Hy as [_ Hy]. cbn [fst] in Hy. unfold in_env_domain in Hy.
  apply inb_true_iff in Hy. exact Hy.
Qed.

Lemma raise_needs_reqs_domain : forall env reqs x,
  In x (env_domain (env_raise env (needs_reqs env reqs))) <-> In x (env_domain env).
Proof.
  intros env reqs x. rewrite env_raise_domain. split.
  - intros [H | H]; [eapply needs_reqs_keys; eauto | exact H].
  - intros H. right. exact H.
Qed.

(** After raising, every requirement on a bound variable is met. *)
Lemma raise_needs_reqs_meets : forall env reqs x r r',
  In (x, r) reqs ->
  env_lookup x (env_raise env (needs_reqs env reqs)) = Some r' ->
  r <=_r r'.
Proof.
  intros env reqs x r r' Hx Hl.
  assert (Hdom : In x (env_domain env)).
  { apply (raise_needs_reqs_domain env reqs). eapply env_lookup_in_domain; eauto. }
  assert (Hin : In (x, r) (needs_reqs env reqs)).
  { unfold needs_reqs. apply filter_In. split; [exact Hx|]. cbn [fst].
    unfold in_env_domain. apply inb_true_iff. exact Hdom. }
  destruct (env_raise_meets env _ x r Hin) as [r'' [Hl'' Hle]].
  rewrite Hl in Hl''. injection Hl'' as <-. exact Hle.
Qed.

Lemma needs_keys : forall env xs r x,
  In x (map fst (needs env xs r)) -> In x (env_domain env).
Proof. intros env xs r x. apply needs_reqs_keys. Qed.

Lemma raise_needs_domain : forall env xs r x,
  In x (env_domain (env_raise env (needs env xs r))) <-> In x (env_domain env).
Proof. intros env xs r x. apply raise_needs_reqs_domain. Qed.

(** After raising, every variable of [xs] that is bound is at least
    [r]. *)
Lemma raise_needs_meets : forall env xs r x r',
  In x xs ->
  env_lookup x (env_raise env (needs env xs r)) = Some r' ->
  r <=_r r'.
Proof.
  intros env xs r x r' Hx Hl. eapply raise_needs_reqs_meets; [|exact Hl].
  apply in_map_iff. exists x. auto.
Qed.

(** Γ meets the requirements [reqs]: every requirement on a variable typed
    by Γ is below its representation in Γ. *)
Definition env_meets (env : Environment) (reqs : list (Var * Representation))
  : Prop :=
  forall x r r', In (x, r) reqs -> env_lookup x env = Some r' -> r <=_r r'.

Lemma raise_needs_reqs_env_meets : forall env reqs,
  env_meets (env_raise env (needs_reqs env reqs)) reqs.
Proof.
  intros env reqs x r r' Hx Hl. eapply raise_needs_reqs_meets; eauto.
Qed.

(** The requirements of an expression are all point-valued (at least ι);
    a mapping respecting an environment that meets them has point-valued
    bindings on the variables of the expression (Lemma 6.3 applies). *)
Lemma env_meets_point_on : forall env m r c,
  env_ok env m -> Id <=_r r -> env_meets env (expr_reqs_at r c) ->
  point_on (expr_vars c) m.
Proof.
  intros env m r c Hok Hr Hm x b Hx Hl.
  destruct (Hok x b Hl) as [r' [Hr' Hle]].
  rewrite <- (expr_reqs_at_keys r c) in Hx. apply in_map_iff in Hx.
  destruct Hx as [[y r0] [Heq Hin]]. cbn [fst] in Heq. subst y.
  pose proof (expr_reqs_at_point r c x r0 Hr Hin) as Hr0.
  pose proof (Hm x r0 r' Hin Hr') as Hle'.
  apply point_val_repr. apply Id_leq_point.
  eapply leq_repr_trans; [exact Hr0|]. eapply leq_repr_trans; [exact Hle' | exact Hle].
Qed.

(** Variables required at ι (grouping variables) are point-valued. *)
Lemma env_meets_ids_point_on : forall env m ks,
  env_ok env m -> env_meets env (map (fun x => (x, Id)) ks) -> point_on ks m.
Proof.
  intros env m ks Hok Hm x b Hx Hl. destruct (Hok x b Hl) as [r [Hr Hle]].
  apply point_val_repr. apply Id_leq_point.
  eapply leq_repr_trans; [|exact Hle]. apply (Hm x Id r); [|exact Hr].
  apply in_map_iff. exists x. auto.
Qed.

Lemma env_meets_incl : forall env reqs1 reqs2,
  (forall xr, In xr reqs1 -> In xr reqs2) ->
  env_meets env reqs2 -> env_meets env reqs1.
Proof.
  intros env reqs1 reqs2 Hincl Hm x r r' Hx Hr. apply (Hm x r r'); [|exact Hr].
  apply Hincl. exact Hx.
Qed.

(** Consequence for the evaluation: variables raised to ν are
    point-valued. *)
Lemma env_ok_needs_point_on : forall env xs m,
  env_ok (env_raise env (needs env xs Value)) m -> point_on xs m.
Proof.
  intros env xs m Hok. eapply env_ok_point_on; [exact Hok|].
  intros x r Hx Hr. pose proof (raise_needs_meets env xs Value x r Hx Hr) as H.
  eapply point_repr_mono; [exact H | reflexivity].
Qed.

(** ** Invariants of the other operators *)

Lemma env_ok_cons : forall env m x t,
  env_ok env m -> env_ok ((x, Value) :: env) ((x, BVal t) :: m).
Proof.
  intros env m x t Hok y b Hl. simpl in Hl |- *.
  destruct (Var_eq_dec y x) as [-> | Hneq].
  - injection Hl as <-. exists Value. split; [reflexivity | apply leq_repr_refl].
  - apply (Hok y b Hl).
Qed.

Lemma env_ok_restrict : forall env m vars,
  env_ok env m -> env_ok (env_restrict env vars) (restrict vars m).
Proof.
  intros env m vars Hok x b Hl. unfold restrict in Hl.
  destruct (memb x vars) eqn:Em.
  - rewrite lookup_filter_keep in Hl by (intros a; cbn [fst]; exact Em).
    destruct (Hok x b Hl) as [r [Hr Hle]]. exists r. split; [|exact Hle].
    unfold env_restrict. rewrite env_lookup_eq in Hr |- *.
    rewrite lookup_filter_keep; [exact Hr|]. intros a. cbn [fst]. exact Em.
  - rewrite lookup_filter_drop in Hl by (intros a; cbn [fst]; exact Em).
    discriminate.
Qed.

Lemma env_ok_refines : forall env m s,
  env_ok env m -> refines s m -> env_ok env s.
Proof.
  intros env m s Hok [_ [_ Hl]] x b' Hb'.
  destruct (Hl x b' Hb') as [b [Hb Heq]]. destruct (Hok x b Hb) as [r [Hr Hle]].
  exists r. split; [exact Hr | rewrite Heq; exact Hle].
Qed.

(** Pointwise environments for quad patterns: a mapping whose bindings have
    exactly the representations listed by the environment, in the same
    order. *)
Lemma env_ok_pointwise : forall (env : Environment) (m : CMapping),
  Forall2 (fun xb xr => fst xb = fst xr /\ binding_repr (snd xb) = snd xr) m env ->
  env_ok env m.
Proof.
  intros env m H. induction H as [| [x b] [y r] m env [Heq Hrepr] _ IH];
    intros z b' Hl; simpl in *; [discriminate|].
  subst y. destruct (Var_eq_dec z x) as [-> | Hneq].
  - injection Hl as <-. exists r. split; [reflexivity | rewrite <- Hrepr; apply leq_repr_refl].
  - apply (IH z b' Hl).
Qed.
