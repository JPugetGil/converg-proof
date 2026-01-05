(** * Representations: Variable Representation Type System
    
    This module defines the type system for variable representations
    in the condensed SPARQL algebra.
*)

Require Import Stdlib.Lists.List.
Require Import ConVerG.RDF.
Import ListNotations.

(** ** Variable Representations *)

(** Four representations form a bounded total order:
    UnboundGraph ≤ Condensed ≤ Id ≤ Value *)
Inductive Representation : Type :=
  | Value        (** Variable bound to an actual RDF term (ν) *)
  | Id           (** Variable bound to a term identifier (ι) *)
  | Condensed    (** Variable bound to (graph_id, version_set) pair (ζ) *)
  | UnboundGraph (** Variable bound to all versioned named graphs (ψ) *).

(** Equality decision for representations. *)
Definition Representation_eq_dec : forall r1 r2 : Representation, {r1 = r2} + {r1 <> r2}.
Proof.
  decide equality.
Defined.

(** ** Total Order on Representations *)

(** The order relation: UnboundGraph ≤ Condensed ≤ Id ≤ Value *)
Definition leq_repr (r1 r2 : Representation) : Prop :=
  match r1, r2 with
  | UnboundGraph, _ => True
  | Condensed, UnboundGraph => False
  | Condensed, _ => True
  | Id, UnboundGraph => False
  | Id, Condensed => False
  | Id, _ => True
  | Value, Value => True
  | Value, _ => False
  end.

Notation "r1 <=_r r2" := (leq_repr r1 r2) (at level 70).

(** Strict order. *)
Definition lt_repr (r1 r2 : Representation) : Prop :=
  leq_repr r1 r2 /\ r1 <> r2.

Notation "r1 <_r r2" := (lt_repr r1 r2) (at level 70).

(** Boolean version of leq. *)
Definition leq_repr_dec (r1 r2 : Representation) : bool :=
  match r1, r2 with
  | UnboundGraph, _ => true
  | Condensed, UnboundGraph => false
  | Condensed, _ => true
  | Id, UnboundGraph => false
  | Id, Condensed => false
  | Id, _ => true
  | Value, Value => true
  | Value, _ => false
  end.

(** ** Lattice Operations *)

(** Greatest lower bound (meet): the minimum representation. *)
Definition meet_repr (r1 r2 : Representation) : Representation :=
  if leq_repr_dec r1 r2 then r1 else r2.

Notation "r1 ⊓ r2" := (meet_repr r1 r2) (at level 40).

(** Least upper bound (join): the maximum representation. *)
Definition join_repr (r1 r2 : Representation) : Representation :=
  if leq_repr_dec r1 r2 then r2 else r1.

Notation "r1 ⊔ r2" := (join_repr r1 r2) (at level 40).

(** ** Properties *)

(** Reflexivity of the order. *)
Lemma leq_repr_refl : forall r, r <=_r r.
Proof.
  destruct r; simpl; auto.
Qed.

(** Transitivity of the order. *)
Lemma leq_repr_trans : forall r1 r2 r3,
  r1 <=_r r2 -> r2 <=_r r3 -> r1 <=_r r3.
Proof.
  intros r1 r2 r3; destruct r1, r2, r3; simpl; auto.
Qed.

(** Antisymmetry of the order. *)
Lemma leq_repr_antisym : forall r1 r2,
  r1 <=_r r2 -> r2 <=_r r1 -> r1 = r2.
Proof.
  intros r1 r2; destruct r1, r2; simpl; auto; intros H1 H2; contradiction.
Qed.

(** Value is the greatest element. *)
Lemma value_greatest : forall r, r <=_r Value.
Proof.
  destruct r; simpl; auto.
Qed.

(** UnboundGraph is the least element. *)
Lemma unboundgraph_least : forall r, UnboundGraph <=_r r.
Proof.
  destruct r; simpl; auto.
Qed.
