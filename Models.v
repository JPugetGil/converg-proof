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

(** condensed_lookup at a matching head entry always succeeds. *)
Lemma condensed_lookup_cons_eq : forall q vs rest,
  condensed_lookup q ((q, vs) :: rest) = Some vs.
Proof.
  intros [s p o g] vs rest. simpl.
  destruct (IRI_eq_dec s s); [|congruence].
  destruct (IRI_eq_dec p p); [|congruence].
  destruct (Term_eq_dec o o); [|congruence].
  destruct (IRI_eq_dec g g); [|congruence].
  reflexivity.
Qed.

(** condensed_lookup succeeds in a mapped list when the quad is present. *)
Lemma condensed_lookup_in_map_eq : forall q qs (f : Quad -> VersionSet),
  In q qs ->
  condensed_lookup q (map (fun q' => (q', f q')) qs) = Some (f q).
Proof.
  intros q qs f Hin.
  induction qs as [|q' rest IH].
  - contradiction.
  - simpl. destruct Hin as [Heq | Hin_rest].
    + subst q'. apply condensed_lookup_cons_eq.
    + destruct (Quad_eq_dec q q') as [Heq|Hneq].
      * subst q'. apply condensed_lookup_cons_eq.
      * destruct q as [qs' qp qo qg].
        destruct q' as [qs'' qp' qo' qg'].
        simpl.
        destruct (IRI_eq_dec qs' qs'');
        [destruct (IRI_eq_dec qp qp');
         [destruct (Term_eq_dec qo qo');
          [destruct (IRI_eq_dec qg qg');
           [subst; exfalso; apply Hneq; reflexivity
           |apply IH; exact Hin_rest]
          |apply IH; exact Hin_rest]
         |apply IH; exact Hin_rest]
        |apply IH; exact Hin_rest].
Qed.

(** The result of condensed_lookup in a mapped list equals f(q). *)
Lemma condensed_lookup_in_map_result : forall q qs (f : Quad -> VersionSet) vs,
  condensed_lookup q (map (fun q' => (q', f q')) qs) = Some vs ->
  vs = f q.
Proof.
  intros q qs f vs H.
  induction qs as [|q' rest IH].
  - simpl in H. discriminate.
  - simpl in H.
    destruct q as [qs' qp qo qg].
    destruct q' as [qs'' qp' qo' qg'].
    simpl in H.
    destruct (IRI_eq_dec qs' qs'').
    + destruct (IRI_eq_dec qp qp').
      * destruct (Term_eq_dec qo qo').
        -- destruct (IRI_eq_dec qg qg').
           ++ inversion H. subst. reflexivity.
           ++ apply IH. exact H.
        -- apply IH. exact H.
      * apply IH. exact H.
    + apply IH. exact H.
Qed.

(** If condensed_lookup returns Some, the entry is in the list. *)
Lemma condensed_lookup_Some_In : forall q vs cm,
  condensed_lookup q cm = Some vs ->
  In (q, vs) cm.
Proof.
  intros q vs cm H.
  induction cm as [|[q' vs'] rest IH].
  - simpl in H. discriminate.
  - simpl in H.
    destruct q as [qs qp qo qg].
    destruct q' as [qs' qp' qo' qg'].
    simpl in H.
    destruct (IRI_eq_dec qs qs').
    + destruct (IRI_eq_dec qp qp').
      * destruct (Term_eq_dec qo qo').
        -- destruct (IRI_eq_dec qg qg').
           ++ inversion H. subst. left. reflexivity.
           ++ right. apply IH. exact H.
        -- right. apply IH. exact H.
      * right. apply IH. exact H.
    + right. apply IH. exact H.
Qed.

(** quad_with_version inverse lemmas. *)
Lemma quad_with_version_to_quad : forall q v,
  versioned_quad_to_quad (quad_with_version q v) = q.
Proof.
  intros [s p o g] v. simpl. reflexivity.
Qed.

Lemma quad_with_version_version : forall q v,
  vq_version (quad_with_version q v) = v.
Proof.
  intros [s p o g] v. simpl. reflexivity.
Qed.

Lemma quad_with_version_inverse : forall vq,
  quad_with_version (versioned_quad_to_quad vq) (vq_version vq) = vq.
Proof.
  intros [s p o g v]. simpl. reflexivity.
Qed.

(** condensed_lookup in condense finds the version set when the quad exists. *)
Lemma condensed_lookup_in_condense : forall vq fm,
  In vq fm ->
  exists vs, condensed_lookup (versioned_quad_to_quad vq) (condense fm) = Some vs /\
             In (vq_version vq) vs.
Proof.
  intros vq fm Hin.
  exists (versions_of_quad (versioned_quad_to_quad vq) fm).
  split.
  - unfold condense, unique_quads.
    apply condensed_lookup_in_map_eq.
    apply in_map. exact Hin.
  - apply in_fm_in_versions. exact Hin.
Qed.

(** ** Main Theorems *)

(** Theorem 4.6: Condensing preserves the flat model.
    condense(d_F) corresponds to d_F. *)
Theorem condense_flatten_identity : forall fm : FlatModel,
  models_correspond fm (condense fm).
Proof.
  intros fm.
  unfold models_correspond, in_flat_model.
  intros vq. split.
  - (* Forward: vq ∈ fm → lookup succeeds with version in set *)
    intro Hin. apply condensed_lookup_in_condense. exact Hin.
  - (* Backward: lookup succeeds with version in set → vq ∈ fm *)
    intros [vs [Hlookup Hversion_in]].
    unfold condense, unique_quads in Hlookup.
    pose proof (condensed_lookup_in_map_result _ _ _ _ Hlookup) as Heq.
    subst vs.
    apply in_versions_of_quad in Hversion_in.
    destruct Hversion_in as [vq' [Hin' [Hquad_eq Hversion_eq]]].
    destruct vq as [s p o g v].
    destruct vq' as [s' p' o' g' v'].
    simpl in *.
    unfold versioned_quad_to_quad in Hquad_eq. simpl in Hquad_eq.
    inversion Hquad_eq. subst s' p' o' g' v'.
    exact Hin'.
Qed.

(** ** Well-formedness for Condensed Models *)

(** A condensed model is well-formed if no quad appears as a key more than once. *)
Definition wf_condensed (cm : CondensedModel) : Prop :=
  NoDup (map fst cm).

(** condensed_lookup under NoDup returns the unique entry's version set. *)
Lemma condensed_lookup_NoDup : forall q vs cm,
  NoDup (map fst cm) ->
  In (q, vs) cm ->
  condensed_lookup q cm = Some vs.
Proof.
  intros q vs cm Hnodup Hin.
  induction cm as [|[q' vs'] rest IH].
  - contradiction.
  - simpl in Hin. destruct Hin as [Heq | Hin_rest].
    + inversion Heq. subst q' vs'.
      apply condensed_lookup_cons_eq.
    + simpl (map fst _) in Hnodup.
      apply NoDup_cons_iff in Hnodup.
      destruct Hnodup as [Hnotin Hnodup_rest].
      destruct q as [qs qp qo qg].
      destruct q' as [qs' qp' qo' qg'].
      simpl.
      destruct (IRI_eq_dec qs qs') as [Hs|Hs].
      * destruct (IRI_eq_dec qp qp') as [Hp|Hp].
        ** destruct (Term_eq_dec qo qo') as [Ho|Ho].
           *** destruct (IRI_eq_dec qg qg') as [Hg|Hg].
               **** subst qs' qp' qo' qg'.
                    exfalso. apply Hnotin.
                    apply in_map_iff. exists (mkQuad qs qp qo qg, vs).
                    split; [reflexivity|exact Hin_rest].
               **** apply IH; assumption.
           *** apply IH; assumption.
        ** apply IH; assumption.
      * apply IH; assumption.
Qed.

(** If (q, vs) is in cm and v is in vs, then quad_with_version q v is in flatten cm. *)
Lemma in_flatten : forall q vs v cm,
  In (q, vs) cm ->
  In v vs ->
  In (quad_with_version q v) (flatten cm).
Proof.
  intros q vs v cm Hqvs Hv.
  unfold flatten.
  apply in_flat_map.
  exists (q, vs). split.
  - exact Hqvs.
  - simpl. apply in_map. exact Hv.
Qed.

(** If vq is in flatten cm, then there exists an entry in cm it came from. *)
Lemma in_flatten_inv : forall vq cm,
  In vq (flatten cm) ->
  exists q vs, In (q, vs) cm /\
               vq = quad_with_version q (vq_version vq) /\
               versioned_quad_to_quad vq = q /\
               In (vq_version vq) vs.
Proof.
  intros vq cm Hin.
  unfold flatten in Hin.
  apply in_flat_map in Hin.
  destruct Hin as [[q vs] [Hqvs Hvq]].
  simpl in Hvq.
  apply in_map_iff in Hvq.
  destruct Hvq as [v [Heq Hvin]].
  exists q, vs.
  subst vq.
  rewrite quad_with_version_to_quad.
  rewrite quad_with_version_version.
  auto.
Qed.

(** Theorem 4.7: Flattening preserves the condensed model (under well-formedness).
    flatten(d_C) corresponds to d_C. *)
Theorem flatten_condense_identity : forall cm : CondensedModel,
  wf_condensed cm ->
  models_correspond (flatten cm) cm.
Proof.
  intros cm Hwf.
  unfold models_correspond, in_flat_model.
  intros vq. split.
  - (* Forward: In vq (flatten cm) → lookup succeeds *)
    intro Hin.
    apply in_flatten_inv in Hin.
    destruct Hin as [q [vs [Hqvs [Hvq [Hquad Hvin]]]]].
    exists vs. split.
    + rewrite Hquad.
      apply condensed_lookup_NoDup; [exact Hwf | exact Hqvs].
    + exact Hvin.
  - (* Backward: lookup succeeds → In vq (flatten cm) *)
    intros [vs [Hlookup Hversion]].
    apply condensed_lookup_Some_In in Hlookup.
    rewrite <- (quad_with_version_inverse vq).
    eapply in_flatten; eassumption.
Qed.
