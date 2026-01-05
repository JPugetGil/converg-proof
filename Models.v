(** * Models: Flat and Condensed Dataset Models
    
    This module defines the flat and condensed representations
    for versioned RDF datasets, along with the transformation
    functions between them.
*)

From Stdlib Require Import Ensembles.
From Stdlib Require Import List.
Require Import ConVerG.RDF.
Require Import ConVerG.Versioning.
Import ListNotations.

(** ** Flat Model *)

(** The flat model represents a dataset as a set of versioned quads.
    Each triple is augmented with a named graph and version. *)
Definition FlatModel := FiniteSet VersionedQuad.

(** Check if a versioned quad is in a flat model. *)
Definition in_flat_model (vq : VersionedQuad) (fm : FlatModel) : Prop :=
  In vq fm.

(** Get all versions of the dataset. *)
Definition flat_model_versions (fm : FlatModel) : VersionSet :=
  map vq_version fm.

(** ** Condensed Model *)

(** The condensed model maps quads to their valid version sets.
    Represented as an association list from Quad to VersionSet. *)
Definition CondensedModel := list (Quad * VersionSet).

(** Look up the version set for a quad in a condensed model. *)
Fixpoint condensed_lookup (q : Quad) (cm : CondensedModel) : option VersionSet :=
  match cm with
  | [] => None
  | (q', vs) :: rest =>
      if IRI_eq_dec (quad_subject q) (quad_subject q') then
        if IRI_eq_dec (quad_predicate q) (quad_predicate q') then
          if Term_eq_dec (quad_object q) (quad_object q') then
            if IRI_eq_dec (quad_graph q) (quad_graph q') then
              Some vs
            else condensed_lookup q rest
          else condensed_lookup q rest
        else condensed_lookup q rest
      else condensed_lookup q rest
  end.

(** Domain of the condensed model: quads that appear in at least one version. *)
Definition condensed_domain (cm : CondensedModel) : list Quad :=
  map fst cm.

(** ** Condensation Function *)

(** Helper: collect all versions where a quad appears in the flat model. *)
Definition versions_of_quad (q : Quad) (fm : FlatModel) : VersionSet :=
  map vq_version 
    (filter (fun vq => 
      if IRI_eq_dec (quad_subject q) (vq_subject vq) then
        if IRI_eq_dec (quad_predicate q) (vq_predicate vq) then
          if Term_eq_dec (quad_object q) (vq_object vq) then
            if IRI_eq_dec (quad_graph q) (vq_graph vq) then true
            else false
          else false
        else false
      else false) fm).

(** Get unique quads from a flat model. *)
Definition unique_quads (fm : FlatModel) : list Quad :=
  map versioned_quad_to_quad fm. (* Note: would need dedup in real impl *)

(** Condensation: transform a flat model into a condensed model.
    C(q) = { v | (s, p, o, g, v) ∈ d_F } *)
Definition condense (fm : FlatModel) : CondensedModel :=
  map (fun q => (q, versions_of_quad q fm)) (unique_quads fm).

(** ** Flattening Function *)

(** Flattening: transform a condensed model into a flat model.
    F = { (s, p, o, g, v) | v ∈ d_C(s, p, o, g) } *)
Definition flatten (cm : CondensedModel) : FlatModel :=
  flat_map (fun qvs : Quad * VersionSet =>
    map (fun v => quad_with_version (fst qvs) v) (snd qvs)
  ) cm.

(** ** Model Correspondence *)

(** Two models correspond if they represent the same data. *)
Definition models_correspond (fm : FlatModel) (cm : CondensedModel) : Prop :=
  forall vq : VersionedQuad,
    in_flat_model vq fm <->
    exists vs, condensed_lookup (versioned_quad_to_quad vq) cm = Some vs /\
               In (vq_version vq) vs.

(** ** Main Theorems *)

(** Theorem: Condensing then flattening returns the original flat model.
    condense ∘ flatten (d_F) = d_F *)
Theorem condense_flatten_identity : forall fm : FlatModel,
  (* Note: equality up to permutation and deduplication *)
  models_correspond fm (condense fm).
Proof.
  (* Proof sketch from LaTeX:
     1. Show condense ∘ flatten (d_F) ⊆ d_F
     2. Show d_F ⊆ condense ∘ flatten (d_F)
     For any (s,p,o,g,v) ∈ d_F, v ∈ condense(d_F)(s,p,o,g),
     so (s,p,o,g,v) ∈ flatten(condense(d_F)). *)
Admitted.

(** Theorem: Flattening then condensing returns the original condensed model.
    flatten ∘ condense (d_C) = d_C *)
Theorem flatten_condense_identity : forall cm : CondensedModel,
  forall q : Quad,
    condensed_lookup q cm = condensed_lookup q (condense (flatten cm)).
Proof.
  (* Proof sketch from LaTeX:
     Let V^C = condense(flatten(d_C))(q)
     Then V^C = { v | (s,p,o,g,v) ∈ flatten(d_C) }
              = { v | v ∈ d_C(s,p,o,g) }
              = d_C(s,p,o,g) *)
Admitted.
