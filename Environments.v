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

(** Placeholder for expression type - will be defined in FlatAlgebra.v *)
Parameter Expr : Type.

(** Provability: env ⊢ e means expression e is well-typed under environment env. *)
Parameter typing : Environment -> Expr -> Prop.

Notation "env ⊢ e" := (typing env e) (at level 70).

(** ** Optimal Representation *)

(** The optimal representation function computes the environment where
    all variables are reduced to the lowest representation that still
    satisfies all typing constraints.
    
    R*(e) = ⊓ { Γ | Γ ⊢ e }
*)
Definition optimal_repr (e : Expr) : Environment :=
  (* This would require collecting all valid environments for e
     and computing their meet. For now, axiomatized. *)
  []. (* Placeholder *)

(** ** Greatest Environment Typing Lemma *)

(** Helper: greatest upper bound of a set of environments. *)
Definition greatest_env (envs : list Environment) : Environment :=
  map (fun x =>
    match fold_right
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
    | Some r => (x, r)
    | None => (x, Value) (* fallback to greatest *)
    end)
    (flat_map env_domain envs).

(** Lemma: If all environments in a set can type an expression,
    then the greatest environment can also type it.
    
    ∀Γ ∈ Δ, Γ ⊢ e  ⟹  ≥_r(Δ) ⊢ e
*)
Lemma greatest_environment_typing : forall (envs : list Environment) (e : Expr),
  (forall env, In env envs -> typing env e) ->
  typing (greatest_env envs) e.
Proof.
  (* Proof requires induction on expression structure
     and showing that type requirements only decrease
     as representations increase. *)
Admitted.
