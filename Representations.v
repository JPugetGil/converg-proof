(** * Representations: Variable Representations and Dictionary Encoding

    Thesis, Definition 5.3 (dictionary encoding) and Definition 5.18
    (variable representations).

    The four representations form the bounded total order
    [UnboundGraph ≤ Condensed ≤ Id ≤ Value]  (ψ ≤ ζ ≤ ι ≤ ν).
*)

From Stdlib Require Import List Bool Lia.
Require Import ConVerG.RDF.
Import ListNotations.

(** ** Dictionary Encoding (Definition 5.3) *)

(** Terms are stored as integer identifiers.  The thesis assumes that the
    encoding [ι-to-ν : N → T] is a bijection; we take both directions as
    parameters with the two inverse laws as modeling assumptions. *)
Parameter id_to_val : nat -> Term.
Parameter val_to_id : Term -> nat.

Axiom id_to_val_to_id : forall t, id_to_val (val_to_id t) = t.
Axiom val_to_id_to_val : forall n, val_to_id (id_to_val n) = n.

Lemma id_to_val_injective : forall n1 n2,
  id_to_val n1 = id_to_val n2 -> n1 = n2.
Proof.
  intros n1 n2 H.
  rewrite <- (val_to_id_to_val n1), <- (val_to_id_to_val n2), H. reflexivity.
Qed.

Lemma val_to_id_injective : forall t1 t2,
  val_to_id t1 = val_to_id t2 -> t1 = t2.
Proof.
  intros t1 t2 H.
  rewrite <- (id_to_val_to_id t1), <- (id_to_val_to_id t2), H. reflexivity.
Qed.

(** ** Variable Representations (Definition 5.18) *)

Inductive Representation : Type :=
  | Value        (** ν: bound to an actual RDF term *)
  | Id           (** ι: bound to a term identifier *)
  | Condensed    (** ζ: bound to a (named graph, version set) pair *)
  | UnboundGraph (** ψ: ranges over all versioned named graphs *).

Definition Representation_eq_dec :
  forall r1 r2 : Representation, {r1 = r2} + {r1 <> r2}.
Proof. decide equality. Defined.

(** ** Total Order on Representations *)

(** Rank of a representation: the order is the order of the ranks. *)
Definition repr_rank (r : Representation) : nat :=
  match r with
  | UnboundGraph => 0
  | Condensed => 1
  | Id => 2
  | Value => 3
  end.

Definition leq_repr (r1 r2 : Representation) : Prop :=
  repr_rank r1 <= repr_rank r2.

Notation "r1 <=_r r2" := (leq_repr r1 r2) (at level 70).

Definition lt_repr (r1 r2 : Representation) : Prop :=
  leq_repr r1 r2 /\ r1 <> r2.

Notation "r1 <_r r2" := (lt_repr r1 r2) (at level 70).

Definition leq_repr_dec (r1 r2 : Representation) : bool :=
  Nat.leb (repr_rank r1) (repr_rank r2).

Lemma leq_repr_dec_true : forall r1 r2,
  leq_repr_dec r1 r2 = true <-> r1 <=_r r2.
Proof. intros. unfold leq_repr_dec, leq_repr. apply PeanoNat.Nat.leb_le. Qed.

(** ** Lattice Operations *)

(** Meet: the lower of the two representations. *)
Definition meet_repr (r1 r2 : Representation) : Representation :=
  if leq_repr_dec r1 r2 then r1 else r2.

Notation "r1 ⊓ r2" := (meet_repr r1 r2) (at level 40).

(** Join: the higher of the two representations. *)
Definition join_repr (r1 r2 : Representation) : Representation :=
  if leq_repr_dec r1 r2 then r2 else r1.

Notation "r1 ⊔ r2" := (join_repr r1 r2) (at level 40).

(** ** Properties *)

Lemma leq_repr_refl : forall r, r <=_r r.
Proof. intros r. unfold leq_repr. apply le_n. Qed.

Lemma leq_repr_trans : forall r1 r2 r3,
  r1 <=_r r2 -> r2 <=_r r3 -> r1 <=_r r3.
Proof. intros r1 r2 r3. unfold leq_repr. apply PeanoNat.Nat.le_trans. Qed.

Lemma leq_repr_antisym : forall r1 r2,
  r1 <=_r r2 -> r2 <=_r r1 -> r1 = r2.
Proof.
  intros r1 r2; destruct r1, r2; unfold leq_repr; simpl; intros;
    reflexivity || lia.
Qed.

Lemma leq_repr_total : forall r1 r2, r1 <=_r r2 \/ r2 <=_r r1.
Proof. intros r1 r2. unfold leq_repr. apply PeanoNat.Nat.le_ge_cases. Qed.

Lemma value_greatest : forall r, r <=_r Value.
Proof. destruct r; unfold leq_repr; simpl; lia. Qed.

Lemma unboundgraph_least : forall r, UnboundGraph <=_r r.
Proof. destruct r; unfold leq_repr; simpl; lia. Qed.

Lemma join_repr_ub_l : forall r1 r2, r1 <=_r r1 ⊔ r2.
Proof.
  intros r1 r2. unfold join_repr.
  destruct (leq_repr_dec r1 r2) eqn:E.
  - apply leq_repr_dec_true. exact E.
  - apply leq_repr_refl.
Qed.

Lemma join_repr_ub_r : forall r1 r2, r2 <=_r r1 ⊔ r2.
Proof.
  intros r1 r2. unfold join_repr.
  destruct (leq_repr_dec r1 r2) eqn:E.
  - apply leq_repr_refl.
  - unfold leq_repr_dec in E. apply PeanoNat.Nat.leb_gt in E.
    unfold leq_repr. apply PeanoNat.Nat.lt_le_incl. exact E.
Qed.

Lemma join_repr_lub : forall r1 r2 r,
  r1 <=_r r -> r2 <=_r r -> r1 ⊔ r2 <=_r r.
Proof.
  intros r1 r2 r H1 H2. unfold join_repr.
  destruct (leq_repr_dec r1 r2); assumption.
Qed.

Lemma meet_repr_lb_l : forall r1 r2, r1 ⊓ r2 <=_r r1.
Proof.
  intros r1 r2. unfold meet_repr.
  destruct (leq_repr_dec r1 r2) eqn:E.
  - apply leq_repr_refl.
  - unfold leq_repr_dec in E. apply PeanoNat.Nat.leb_gt in E.
    unfold leq_repr. apply PeanoNat.Nat.lt_le_incl. exact E.
Qed.

Lemma meet_repr_lb_r : forall r1 r2, r1 ⊓ r2 <=_r r2.
Proof.
  intros r1 r2. unfold meet_repr.
  destruct (leq_repr_dec r1 r2) eqn:E.
  - apply leq_repr_dec_true. exact E.
  - apply leq_repr_refl.
Qed.

Lemma meet_repr_glb : forall r1 r2 r,
  r <=_r r1 -> r <=_r r2 -> r <=_r r1 ⊓ r2.
Proof.
  intros r1 r2 r H1 H2. unfold meet_repr.
  destruct (leq_repr_dec r1 r2); assumption.
Qed.

(** Point-valued representations: those that denote a single term. *)
Definition point_repr (r : Representation) : bool :=
  match r with
  | Value | Id => true
  | Condensed | UnboundGraph => false
  end.

Lemma point_repr_mono : forall r1 r2,
  r1 <=_r r2 -> point_repr r1 = true -> point_repr r2 = true.
Proof.
  intros r1 r2; destruct r1, r2; unfold leq_repr; simpl; intros;
    reflexivity || discriminate || lia.
Qed.

Lemma Id_leq_point : forall r, Id <=_r r -> point_repr r = true.
Proof. intros r H. eapply point_repr_mono; eauto. Qed.
