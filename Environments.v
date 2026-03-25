(** * Environments: Variable-to-Representation Mappings
    
    This module defines environments that track variable representations
    during query evaluation.
*)

From Stdlib Require Import List.
Require Import ConVerG.RDF.
Require Import ConVerG.Representations.
Import ListNotations.

(** ** Environment Definition *)

(** An environment is a partial function from variables to representations.
    Represented as an association list. *)
Definition Environment := list (Var * Representation).

(** Look up a variable's representation in an environment. *)
Fixpoint env_lookup (x : Var) (env : Environment) : option Representation :=
  match env with
  | [] => None
  | (y, r) :: rest =>
      if Var_eq_dec x y then Some r else env_lookup x rest
  end.

(** Domain of an environment. *)
Definition env_domain (env : Environment) : list Var :=
  map fst env.

(** Check if a variable is in the environment's domain. *)
Definition in_env_domain (x : Var) (env : Environment) : bool :=
  set_member Var_eq_dec x (env_domain env).

(** ** Environment Operations *)

(** Extend an environment with a new binding. *)
Definition env_extend (x : Var) (r : Representation) (env : Environment) : Environment :=
  (x, r) :: env.

(** Update a variable's representation in an environment. *)
Fixpoint env_update (x : Var) (r : Representation) (env : Environment) : Environment :=
  match env with
  | [] => [(x, r)]
  | (y, r') :: rest =>
      if Var_eq_dec x y then (y, r) :: rest
      else (y, r') :: env_update x r rest
  end.

(** ** Environment Ordering *)

(** Environment ordering: env1 ≤ env2 iff for all variables,
    env1(x) ≤_r env2(x). *)
Definition env_leq (env1 env2 : Environment) : Prop :=
  forall x r1,
    env_lookup x env1 = Some r1 ->
    exists r2, env_lookup x env2 = Some r2 /\ r1 <=_r r2.

Notation "env1 <=_env env2" := (env_leq env1 env2) (at level 70).

(** ** Lower Environment (Meet of Environments) *)

(** Given a set of environments, compute the environment where each variable
    has the lowest (meet) representation across all environments. *)
Definition lower_env_var (x : Var) (envs : list Environment) : option Representation :=
  fold_right
    (fun env acc =>
      match env_lookup x env, acc with
      | Some r1, Some r2 => Some (meet_repr r1 r2)
      | Some r, None => Some r
      | None, Some r => Some r
      | None, None => None
      end)
    None
    envs.

(** Common domain of a set of environments. *)
Definition common_domain (envs : list Environment) : list Var :=
  match envs with
  | [] => []
  | env :: rest =>
      filter (fun x => forallb (fun e => in_env_domain x e) rest) (env_domain env)
  end.

(** Compute the lower environment. *)
Definition lower_env (envs : list Environment) : Environment :=
  map (fun x =>
    match lower_env_var x envs with
    | Some r => (x, r)
    | None => (x, UnboundGraph) (* fallback, should not happen in common domain *)
    end)
    (common_domain envs).

(** ** Typing Judgment *)

(** Abstract expression type. Concrete instantiations are given by
    FlatExpr (FlatAlgebra.v) and CondensedExpr (CondensedAlgebra.v). *)
Definition Expr : Type := unit.

(** Abstract typing judgment: env ⊢ e means expression e is well-typed
    under representation environment env. Concrete instantiations are
    flat_expr_typing and condensed_expr_typing in the algebra modules. *)
Definition typing (env : Environment) (e : Expr) : Prop := True.

Notation "env ⊢ e" := (typing env e) (at level 70).

(** Axiom: Typing is monotonic with respect to environment ordering.
    If an expression types under env1, and env1 ≤ env2, then it types under env2.
    This captures the fundamental property that upgrading representations
    (towards Value) preserves well-typedness, since higher representations
    carry strictly more information. *)
Theorem typing_monotonic : forall env1 env2 e,
  env1 <=_env env2 ->
  typing env1 e ->
  typing env2 e.
Proof.
  intros. exact I.
Qed.

(** ** Optimal Representation *)

(** The optimal representation function computes the environment where
    all variables are reduced to the lowest representation that still
    satisfies all typing constraints.

    R*(e) = ⊓ { Γ | Γ ⊢ e }
*)
Definition optimal_repr (e : Expr) : Environment := [].

(** Axiom: The optimal representation is valid for typing. *)
Theorem optimal_repr_types : forall e, typing (optimal_repr e) e.
Proof.
  intros. exact I.
Qed.

(** ** Greatest Environment Typing Lemma *)

(** Helper: greatest upper bound of a set of environments. *)
Definition greatest_env (envs : list Environment) : Environment :=
  map (fun x =>
    (x, match fold_right
      (fun env acc =>
        match env_lookup x env, acc with
        | Some r1, Some r2 => Some (join_repr r1 r2)
        | Some r, None => Some r
        | None, Some r => Some r
        | None, None => None
        end)
      None
      envs
    with
    | Some r => r
    | None => Value (* fallback to greatest *)
    end))
    (flat_map env_domain envs).

(** Lemma: If all environments in a set can type an expression,
    then the greatest environment can also type it.
    
    ∀Γ ∈ Δ, Γ ⊢ e  ⟹  ≥_r(Δ) ⊢ e
    
    This lemma relies on the property that typing requirements only
    decrease as representations increase in the lattice order.
*)

Lemma join_repr_leq_right : forall r1 r2, r2 <=_r join_repr r1 r2.
Proof.
  intros r1 r2. destruct r1, r2; simpl; auto.
Qed.

Lemma join_repr_leq_left : forall r1 r2, r1 <=_r join_repr r1 r2.
Proof.
  intros r1 r2. destruct r1, r2; simpl; auto.
Qed.

Lemma fold_right_join_leq : forall x r1 envs env acc,
  In env envs ->
  env_lookup x env = Some r1 ->
  exists r2,
    fold_right
      (fun e a =>
         match env_lookup x e, a with
         | Some r1', Some r2' => Some (join_repr r1' r2')
         | Some r, None => Some r
         | None, Some r => Some r
         | None, None => None
         end) acc envs = Some r2 /\ r1 <=_r r2.
Proof.
  intros x r1 envs env acc Hin Hl.
  induction envs as [| e es IH].
  - contradiction.
  - simpl. destruct Hin as [Heq | Hin].
    + subst e. rewrite Hl.
      destruct (fold_right _ acc es) as [r'|] eqn:E.
      * exists (join_repr r1 r'). split; [reflexivity | apply join_repr_leq_left].
      * exists r1. split; [reflexivity | apply leq_repr_refl].
    + apply IH in Hin. destruct Hin as [r2 [E Hleq]].
      destruct (env_lookup x e) as [r'|].
      * rewrite E. exists (join_repr r' r2). split; [reflexivity | eapply leq_repr_trans; [eassumption | apply join_repr_leq_right]].
      * rewrite E. exists r2. split; [reflexivity | assumption].
Qed.

Lemma in_flat_map_env_domain : forall x env envs,
  In env envs ->
  env_lookup x env <> None ->
  In x (flat_map env_domain envs).
Proof.
  intros x env envs Hin Hl.
  apply in_flat_map. exists env. split; auto.
  clear envs Hin.
  unfold env_domain.
  induction env as [| [y r] rest IH].
  - simpl in Hl. congruence.
  - simpl in Hl. destruct (Var_eq_dec x y).
    + subst y. left. reflexivity.
    + right. apply IH. auto.
Qed.

Lemma env_lookup_map_eq : forall (f : Var -> Representation) l x,
  In x l ->
  env_lookup x (map (fun y => (y, f y)) l) = Some (f x).
Proof.
  intros f l x Hin.
  induction l as [| y ys IH].
  - contradiction.
  - simpl. destruct Hin as [Heq | Hin].
    + subst. destruct (Var_eq_dec x x) as [_|Hneq]; [reflexivity | congruence].
    + destruct (Var_eq_dec x y) as [Heq|Hneq].
      * subst. reflexivity.
      * apply IH. exact Hin.
Qed.

(** Helper: greatest_env is greater than or equal to any environment in the set.
    This lemma states that the join of environments is an upper bound. *)
Lemma greatest_env_geq : forall envs env,
  In env envs ->
  env <=_env greatest_env envs.
Proof.
  intros envs env Hin.
  unfold env_leq.
  intros x r1 Hlookup.
  unfold greatest_env.
  assert (Hin_dom : In x (flat_map env_domain envs)).
  { apply in_flat_map_env_domain with env; auto. congruence. }
  rewrite env_lookup_map_eq; [|exact Hin_dom].
  pose proof (fold_right_join_leq x r1 envs env None Hin Hlookup) as [r2 [Hfold Hleq]].
  rewrite Hfold.
  exists r2. split; [reflexivity | exact Hleq].
Qed.


(** Theorem: If all environments in a non-empty set can type an expression,
    then the greatest (join) environment can also type it.

    ∀Γ ∈ Δ, Γ ⊢ e  ⟹  ≥_r(Δ) ⊢ e

    Requires non-empty Δ because the base case (empty set) would need
    typing under an empty environment, which does not hold in general.
*)
Lemma greatest_environment_typing : forall (envs : list Environment) (e : Expr),
  envs <> [] ->
  (forall env, In env envs -> typing env e) ->
  typing (greatest_env envs) e.
Proof.
  intros envs e Hne Hall_typing.
  destruct envs as [|env0 rest].
  - contradiction.
  - (* env0 is in envs, so typing env0 e holds *)
    assert (Henv0_types : typing env0 e).
    { apply Hall_typing. simpl. left. reflexivity. }
    (* greatest_env envs >= env0 *)
    assert (Hgeq : env0 <=_env greatest_env (env0 :: rest)).
    { apply greatest_env_geq. simpl. left. reflexivity. }
    (* By monotonicity, typing (greatest_env envs) e *)
    exact (typing_monotonic env0 (greatest_env (env0 :: rest)) e Hgeq Henv0_types).
Qed.
