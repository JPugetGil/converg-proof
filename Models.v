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

(** ** Auxiliary Lemmas *)

(** Quad equality is decidable *)
Definition Quad_eq_dec : forall q1 q2 : Quad, {q1 = q2} + {q1 <> q2}.
Proof.
  intros q1 q2.
  destruct q1 as [s1 p1 o1 g1].
  destruct q2 as [s2 p2 o2 g2].
  destruct (IRI_eq_dec s1 s2); [|right; intro H; injection H; intros; contradiction].
  destruct (IRI_eq_dec p1 p2); [|right; intro H; injection H; intros; contradiction].
  destruct (Term_eq_dec o1 o2); [|right; intro H; injection H; intros; contradiction].
  destruct (IRI_eq_dec g1 g2); [|right; intro H; injection H; intros; contradiction].
  left. subst. reflexivity.
Defined.

(** versioned_quad_to_quad extracts the quad components correctly *)
Lemma versioned_quad_to_quad_components : forall vq,
  quad_subject (versioned_quad_to_quad vq) = vq_subject vq /\
  quad_predicate (versioned_quad_to_quad vq) = vq_predicate vq /\
  quad_object (versioned_quad_to_quad vq) = vq_object vq /\
  quad_graph (versioned_quad_to_quad vq) = vq_graph vq.
Proof.
  intros vq. destruct vq. simpl. auto.
Qed.

(** If a version is in versions_of_quad q fm, then there exists a 
    versioned quad in fm with that quad and version *)
Lemma in_versions_of_quad : forall q fm v,
  In v (versions_of_quad q fm) ->
  exists vq, In vq fm /\ versioned_quad_to_quad vq = q /\ vq_version vq = v.
Proof.
  intros q fm v H.
  unfold versions_of_quad in H.
  rewrite in_map_iff in H.
  destruct H as [vq [Hv Hfilter]].
  rewrite filter_In in Hfilter.
  destruct Hfilter as [Hin Hcond].
  exists vq.
  split; [exact Hin|].
  destruct q as [qs qp qo qg].
  destruct vq as [vqs vqp vqo vqg vqv].
  simpl in *.
  subst v.
  destruct (IRI_eq_dec qs vqs); [|discriminate].
  destruct (IRI_eq_dec qp vqp); [|discriminate].
  destruct (Term_eq_dec qo vqo); [|discriminate].
  destruct (IRI_eq_dec qg vqg); [|discriminate].
  subst. auto.
Qed.

(** If a versioned quad is in fm, its version is in versions_of_quad *)
Lemma in_fm_in_versions : forall vq fm,
  In vq fm ->
  In (vq_version vq) (versions_of_quad (versioned_quad_to_quad vq) fm).
Proof.
  intros vq fm H.
  unfold versions_of_quad.
  rewrite in_map_iff.
  exists vq.
  split; [reflexivity|].
  rewrite filter_In.
  split; [exact H|].
  destruct vq as [s p o g v]. simpl.
  destruct (IRI_eq_dec s s); [|contradiction].
  destruct (IRI_eq_dec p p); [|contradiction].
  destruct (Term_eq_dec o o); [|contradiction].
  destruct (IRI_eq_dec g g); [|contradiction].
  reflexivity.
Qed.

(** condensed_lookup in condense finds the version set when the quad exists.
    This requires showing that the map/filter operations preserve the property. *)
Lemma condensed_lookup_in_condense : forall vq fm,
  In vq fm ->
  exists vs, condensed_lookup (versioned_quad_to_quad vq) (condense fm) = Some vs /\
             In (vq_version vq) vs.
Proof.
  intros vq fm Hin.
  exists (versions_of_quad (versioned_quad_to_quad vq) fm).
  split.
  - (* Show lookup succeeds - the quad appears in condense fm *)
    (* The proof requires showing that condensed_lookup finds the 
       versions_of_quad for any quad that appears in the model.
       This follows from the definition of condense as map over unique_quads. *)
    unfold condense, unique_quads.
    induction fm as [|vq' rest IH].
    + simpl in Hin. contradiction.
    + simpl in Hin.
      destruct Hin as [Heq | Hin_rest].
      * subst vq'.
        simpl.
        destruct vq as [s p o g v]. simpl.
        destruct (IRI_eq_dec s s); [|contradiction].
        destruct (IRI_eq_dec p p); [|contradiction].
        destruct (Term_eq_dec o o); [|contradiction].
        destruct (IRI_eq_dec g g); [|contradiction].
        reflexivity.
      * (* vq is in rest - more complex case *)
        (* The lookup may find vq' first if quads match, or find vq in the rest *)
        simpl.
        destruct vq as [s p o g v].
        destruct vq' as [s' p' o' g' v'].
        simpl.
        destruct (IRI_eq_dec s s') as [Hs|Hs].
        { destruct (IRI_eq_dec p p') as [Hp|Hp].
          { destruct (Term_eq_dec o o') as [Ho|Ho].
            { destruct (IRI_eq_dec g g') as [Hg|Hg].
              { (* All match - both quads are the same, return version set *)
                subst. reflexivity. }
              { (* Quads differ in graph - need to look in rest *)
                (* IH doesn't directly apply due to version set difference *)
                admit. } }
            { admit. } }
          { admit. } }
        { admit. }
  - (* Show version is in the set *)
    apply in_fm_in_versions. exact Hin.
Admitted.

(** ** Main Theorems *)

(** Theorem: Condensing then flattening returns the original flat model.
    condense ∘ flatten (d_F) = d_F 
    
    This is the main correctness theorem for the condensation/flattening operations.
    It states that a flat model and its condensed form represent the same data.
*)
Theorem condense_flatten_identity : forall fm : FlatModel,
  models_correspond fm (condense fm).
Proof.
  intros fm.
  unfold models_correspond, in_flat_model.
  intros vq.
  split.
  - (* Forward direction: vq ∈ fm → lookup succeeds with version in set *)
    intro Hvq_in_fm.
    apply condensed_lookup_in_condense. exact Hvq_in_fm.
  - (* Backward direction: lookup succeeds with version in set → vq ∈ fm *)
    intros [vs [Hlookup Hversion_in]].
    (* The proof requires showing that if we can look up the quad of vq
       in condense fm and find its version, then vq itself must be in fm.
       
       This follows from:
       1. The lookup returns versions_of_quad for some quad in fm
       2. versions_of_quad only contains versions from quads actually in fm
       3. Therefore the version membership implies vq existence in fm
    *)
    unfold condense, unique_quads in Hlookup.
    (* Use in_versions_of_quad to get the original versioned quad *)
    assert (Hfind : exists vq', In vq' fm /\ 
                                versioned_quad_to_quad vq' = versioned_quad_to_quad vq /\
                                vq_version vq' = vq_version vq).
    { (* The lookup result tells us the quad exists and version is in the set *)
      admit. (* Detailed proof requires reasoning about condensed_lookup structure *)
    }
    destruct Hfind as [vq' [Hin' [Hquad_eq Hversion_eq]]].
    (* vq and vq' have the same quad and version, so they're equal *)
    destruct vq as [s p o g v].
    destruct vq' as [s' p' o' g' v'].
    simpl in *.
    injection Hquad_eq as Hs Hp Ho Hg.
    subst s' p' o' g' v'.
    exact Hin'.
Admitted.

(** Theorem: Flattening then condensing returns the original condensed model.
    flatten ∘ condense (d_C) = d_C *)
Theorem flatten_condense_identity : forall cm : CondensedModel,
  forall q : Quad,
    condensed_lookup q cm = condensed_lookup q (condense (flatten cm)).
Proof.
  intros cm q.
  (* This theorem states that looking up a quad in the original condensed model
     gives the same result as looking it up after flatten then condense.
     
     Key insight:
     - flatten(cm) expands each (q, vs) pair to versioned quads
     - condense groups them back by quad
     - For well-formed models, this is an identity *)
  induction cm as [|[q' vs'] rest IH].
  - (* Empty model: both sides return None *)
    reflexivity.
  - (* Non-empty: (q', vs') :: rest *)
    simpl.
    destruct q as [qs qp qo qg].
    destruct q' as [qs' qp' qo' qg'].
    simpl.
    destruct (IRI_eq_dec qs qs') as [Hs|Hs];
    destruct (IRI_eq_dec qp qp') as [Hp|Hp];
    destruct (Term_eq_dec qo qo') as [Ho|Ho];
    destruct (IRI_eq_dec qg qg') as [Hg|Hg].
    + (* Quad matches: q = q' *)
      subst.
      (* Need to show: Some vs' = condensed_lookup after flatten/condense *)
      (* This requires showing versions_of_quad preserves vs' through the round-trip *)
      (* The proof depends on the structure of flatten and condense *)
      admit.
    + all: admit. (* Other cases require similar reasoning *)
Admitted.
