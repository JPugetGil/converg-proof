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
Parameter Version : Type.
Parameter Version_eq_dec : forall v1 v2 : Version, {v1 = v2} + {v1 <> v2}.

(** The set of all versions. *)
Definition VersionSet := FiniteSet Version.

(** ** Versioned IRI *)

(** A versioned IRI associates an IRI with a specific snapshot.
    It serves as a unique identifier for a named graph at a particular version. *)
Parameter VersionedIRI : Type.
Parameter VersionedIRI_eq_dec : forall vi1 vi2 : VersionedIRI, {vi1 = vi2} + {vi1 <> vi2}.

(** The bijective function that maps a version and named graph IRI 
    to a versioned IRI. *)
Parameter vi : Version -> IRI -> VersionedIRI.

(** Axiom: vi is injective in both arguments. *)
Axiom vi_injective : forall v1 v2 g1 g2,
  vi v1 g1 = vi v2 g2 -> v1 = v2 /\ g1 = g2.

(** Inverse functions to retrieve the version and named graph from a versioned IRI. *)
Parameter vi_inv_version : VersionedIRI -> Version.
Parameter vi_inv_graph : VersionedIRI -> IRI.

(** Axioms for inverse functions. *)
Axiom vi_inv_version_correct : forall v g,
  vi_inv_version (vi v g) = v.

Axiom vi_inv_graph_correct : forall v g,
  vi_inv_graph (vi v g) = g.

Axiom vi_inverse_complete : forall vir,
  vi (vi_inv_version vir) (vi_inv_graph vir) = vir.

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
