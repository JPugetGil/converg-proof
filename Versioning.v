(** * Versioning: Version and Versioned IRI Definitions
    
    This module defines versioning primitives for RDF data,
    including versioned IRIs and versioned quads.
*)

From Stdlib Require Import Ensembles.
From Stdlib Require Import List.
Require Import ConVerG.RDF.
Import ListNotations.

(** ** Version Type *)

(** A version represents a snapshot of the RDF data at a given point in time. *)
Definition Version : Type := nat.
Definition Version_eq_dec : forall v1 v2 : Version, {v1 = v2} + {v1 <> v2} := PeanoNat.Nat.eq_dec.

(** The set of all versions. *)
Definition VersionSet := FiniteSet Version.

(** ** Versioned IRI *)

(** A versioned IRI associates an IRI with a specific snapshot.
    It serves as a unique identifier for a named graph at a particular version. *)
Definition VersionedIRI : Type := (Version * IRI)%type.

Definition VersionedIRI_eq_dec : forall vi1 vi2 : VersionedIRI, {vi1 = vi2} + {vi1 <> vi2}.
Proof.
  intros [v1 i1] [v2 i2].
  destruct (Version_eq_dec v1 v2).
  - destruct (IRI_eq_dec i1 i2).
    + left. subst. reflexivity.
    + right. intro H. inversion H. contradiction.
  - right. intro H. inversion H. contradiction.
Defined.

(** The bijective function that maps a version and named graph IRI 
    to a versioned IRI. *)
Definition vi (v : Version) (g : IRI) : VersionedIRI := (v, g).

(** Lemma: vi is injective in both arguments. *)
Lemma vi_injective : forall v1 v2 g1 g2,
  vi v1 g1 = vi v2 g2 -> v1 = v2 /\ g1 = g2.
Proof.
  intros v1 v2 g1 g2 H.
  inversion H. auto.
Qed.

(** Inverse functions to retrieve the version and named graph from a versioned IRI. *)
Definition vi_inv_version (vir : VersionedIRI) : Version := fst vir.
Definition vi_inv_graph (vir : VersionedIRI) : IRI := snd vir.

(** Lemmas for inverse functions. *)
Lemma vi_inv_version_correct : forall v g,
  vi_inv_version (vi v g) = v.
Proof. reflexivity. Qed.

Lemma vi_inv_graph_correct : forall v g,
  vi_inv_graph (vi v g) = g.
Proof. reflexivity. Qed.

Lemma vi_inverse_complete : forall vir,
  vi (vi_inv_version vir) (vi_inv_graph vir) = vir.
Proof.
  intros [v i]. reflexivity.
Qed.

(** ** Versioned Quad *)

(** A versioned quad is a quintuplet where the quad is valid at a specific version. *)
Record VersionedQuad : Type := mkVersionedQuad {
  vq_subject : IRI;
  vq_predicate : IRI;
  vq_object : Term;
  vq_graph : IRI;
  vq_version : Version
}.

(** Extract a quad from a versioned quad. *)
Definition versioned_quad_to_quad (vq : VersionedQuad) : Quad :=
  mkQuad (vq_subject vq) (vq_predicate vq) (vq_object vq) (vq_graph vq).

(** Extract version from a versioned quad. *)
Definition versioned_quad_version (vq : VersionedQuad) : Version :=
  vq_version vq.

(** Build a versioned quad from a quad and version. *)
Definition quad_with_version (q : Quad) (v : Version) : VersionedQuad :=
  mkVersionedQuad (quad_subject q) (quad_predicate q) (quad_object q) (quad_graph q) v.

(** ** Version Set Operations *)

Definition version_set_empty : VersionSet := [].

Definition version_set_singleton (v : Version) : VersionSet := [v].

Definition version_set_union (vs1 vs2 : VersionSet) : VersionSet := vs1 ++ vs2.

Definition version_set_intersection (vs1 vs2 : VersionSet) : VersionSet :=
  filter (fun v => set_member Version_eq_dec v vs2) vs1.

Definition version_set_nonempty (vs : VersionSet) : Prop :=
  vs <> [].

(** Cardinality of a version set. *)
Definition version_set_card (vs : VersionSet) : nat := length vs.
