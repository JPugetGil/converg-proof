(** * Environments: Variable-to-Representation Mappings

    Thesis, Definition 5.19 (environments) and the environment operations
    used by the optimal representation function R* (Section 5.4) and by
    the environment transformation Υ (Definition 5.36).
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Representations.
Import ListNotations.

(** ** Environment Definition *)

(** An environment Γ : VAR ⇀ R, represented as an association list. *)
Definition Environment := list (Var * Representation).

Fixpoint env_lookup (x : Var) (env : Environment) : option Representation :=
  match env with
  | [] => None
  | (y, r) :: rest =>
      if Var_eq_dec x y then Some r else env_lookup x rest
  end.

Definition env_domain (env : Environment) : list Var :=
  map fst env.

Definition in_env_domain (x : Var) (env : Environment) : bool :=
  inb Var_eq_dec x (env_domain env).

(** ** Environment Operations *)

Definition env_extend (x : Var) (r : Representation) (env : Environment)
  : Environment :=
  (x, r) :: env.

(** Raise the representation of [x] to at least [r] (adding [x] if it is
    not yet in the domain).  Raising never lowers a representation. *)
Fixpoint env_raise_var (x : Var) (r : Representation) (env : Environment)
  : Environment :=
  match env with
  | [] => [(x, r)]
  | (y, r') :: rest =>
      if Var_eq_dec x y then (y, r' ⊔ r) :: rest
      else (y, r') :: env_raise_var x r rest
  end.

(** Raise every variable of [reqs] in [env]. *)
Definition env_raise (env : Environment) (reqs : list (Var * Representation))
  : Environment :=
  fold_right (fun xr acc => env_raise_var (fst xr) (snd xr) acc) env reqs.

(** Pointwise join of two environments (the least environment above
    both). *)
Definition env_join (env1 env2 : Environment) : Environment :=
  env_raise env1 env2.

(** Restrict an environment to a set of variables. *)
Definition env_restrict (env : Environment) (vars : list Var) : Environment :=
  filter (fun xr => inb Var_eq_dec (fst xr) vars) env.

(** ** Environment Ordering *)

(** env1 ≤ env2 iff env2 binds every variable of env1 to a representation at
    least as informative. *)
Definition env_leq (env1 env2 : Environment) : Prop :=
  forall x r1,
    env_lookup x env1 = Some r1 ->
    exists r2, env_lookup x env2 = Some r2 /\ r1 <=_r r2.

Notation "env1 <=_env env2" := (env_leq env1 env2) (at level 70).

Lemma env_leq_refl : forall env, env <=_env env.
Proof.
  intros env x r H. exists r. split; [exact H | apply leq_repr_refl].
Qed.

Lemma env_leq_trans : forall e1 e2 e3,
  e1 <=_env e2 -> e2 <=_env e3 -> e1 <=_env e3.
Proof.
  intros e1 e2 e3 H12 H23 x r1 H1.
  destruct (H12 x r1 H1) as [r2 [H2 Hle12]].
  destruct (H23 x r2 H2) as [r3 [H3 Hle23]].
  exists r3. split; [exact H3 | eapply leq_repr_trans; eauto].
Qed.

(** ** Lemmas on raising *)

Lemma env_raise_var_lookup_same : forall x r env,
  env_lookup x (env_raise_var x r env) =
  Some (match env_lookup x env with Some r' => r' ⊔ r | None => r end).
Proof.
  intros x r env. induction env as [|[y r'] rest IH]; simpl.
  - destruct (Var_eq_dec x x); [reflexivity | contradiction].
  - destruct (Var_eq_dec x y) as [-> | Hneq]; simpl.
    + destruct (Var_eq_dec y y); [reflexivity | contradiction].
    + destruct (Var_eq_dec x y); [contradiction | exact IH].
Qed.

Lemma env_raise_var_lookup_other : forall x y r env,
  x <> y ->
  env_lookup y (env_raise_var x r env) = env_lookup y env.
Proof.
  intros x y r env Hneq. induction env as [|[z r'] rest IH]; simpl.
  - destruct (Var_eq_dec y x); [congruence | reflexivity].
  - destruct (Var_eq_dec x z) as [-> | Hxz]; simpl.
    + destruct (Var_eq_dec y z); [congruence | reflexivity].
    + destruct (Var_eq_dec y z); [reflexivity | exact IH].
Qed.

Lemma env_raise_var_geq : forall x r env, env <=_env env_raise_var x r env.
Proof.
  intros x r env y r1 H.
  destruct (Var_eq_dec x y) as [-> | Hneq].
  - rewrite env_raise_var_lookup_same, H. eexists. split; [reflexivity|].
    apply join_repr_ub_l.
  - rewrite env_raise_var_lookup_other by exact Hneq. exists r1.
    split; [exact H | apply leq_repr_refl].
Qed.

Lemma env_raise_var_lookup_raised : forall x r env,
  exists r', env_lookup x (env_raise_var x r env) = Some r' /\ r <=_r r'.
Proof.
  intros x r env. rewrite env_raise_var_lookup_same.
  destruct (env_lookup x env).
  - eexists. split; [reflexivity | apply join_repr_ub_r].
  - eexists. split; [reflexivity | apply leq_repr_refl].
Qed.

Lemma env_raise_geq : forall env reqs, env <=_env env_raise env reqs.
Proof.
  intros env reqs. induction reqs as [|[x r] reqs IH]; simpl.
  - apply env_leq_refl.
  - eapply env_leq_trans; [exact IH | apply env_raise_var_geq].
Qed.

Lemma env_lookup_leq_raise_var : forall x r env y r1 r2,
  env_lookup y env = Some r1 ->
  env_lookup y (env_raise_var x r env) = Some r2 ->
  r1 <=_r r2.
Proof.
  intros x r env y r1 r2 H1 H2.
  destruct (env_raise_var_geq x r env y r1 H1) as [r2' [H2' Hle]].
  rewrite H2 in H2'. injection H2' as <-. exact Hle.
Qed.

(** Every requirement is met after raising. *)
Lemma env_raise_meets : forall env reqs x r,
  In (x, r) reqs ->
  exists r', env_lookup x (env_raise env reqs) = Some r' /\ r <=_r r'.
Proof.
  intros env reqs. induction reqs as [|[y r0] reqs IH]; simpl; intros x r Hin.
  - contradiction.
  - destruct Hin as [Heq | Hin].
    + injection Heq as <- <-. apply env_raise_var_lookup_raised.
    + destruct (IH x r Hin) as [r' [Hl Hle]].
      destruct (env_raise_var_geq y r0 (env_raise env reqs) x r' Hl)
        as [r'' [Hl'' Hle'']].
      exists r''. split; [exact Hl'' | eapply leq_repr_trans; eauto].
Qed.

(** Variables in the domain of the raised environment. *)
Lemma env_raise_var_domain : forall x r env y,
  In y (env_domain (env_raise_var x r env)) <->
  y = x \/ In y (env_domain env).
Proof.
  intros x r env y. unfold env_domain in *.
  induction env as [|[z r'] rest IH]; simpl.
  - split; intros [H | []]; subst; left; reflexivity.
  - destruct (Var_eq_dec x z) as [-> | Hneq]; simpl.
    + split; [intros H; right; exact H |
              intros [-> | H]; [left; reflexivity | exact H]].
    + rewrite IH. tauto.
Qed.

Lemma env_raise_domain : forall env reqs y,
  In y (env_domain (env_raise env reqs)) <->
  In y (map fst reqs) \/ In y (env_domain env).
Proof.
  intros env reqs y. induction reqs as [|[x r] reqs IH]; simpl.
  - tauto.
  - rewrite env_raise_var_domain, IH. split.
    + intros [-> | [H | H]];
        [left; left; reflexivity | left; right; exact H | right; exact H].
    + intros [[-> | H] | H];
        [left; reflexivity | right; left; exact H | right; right; exact H].
Qed.

Lemma env_lookup_in_domain : forall x env r,
  env_lookup x env = Some r -> In x (env_domain env).
Proof.
  intros x env r. induction env as [|[y r'] rest IH]; simpl; intros H.
  - discriminate.
  - destruct (Var_eq_dec x y); [left; auto | right; auto].
Qed.

Lemma env_domain_lookup : forall x env,
  In x (env_domain env) -> exists r, env_lookup x env = Some r.
Proof.
  intros x env. induction env as [|[y r'] rest IH]; simpl; intros H.
  - contradiction.
  - destruct (Var_eq_dec x y) as [-> | Hneq].
    + eexists; reflexivity.
    + apply IH. destruct H as [H | H]; [congruence | exact H].
Qed.
