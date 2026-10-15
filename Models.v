(** * Models: Flat and Condensed Dataset Models

    Thesis, Section 5.1 (Definitions 5.2, 5.4, 5.5, 5.6) and
    Theorem 6.1 (inverse properties of condensation and flattening).

    The flat model stores one versioned quad per (quad, version) pair; the
    condensed model maps each quad to the set of versions in which it holds.
*)

From Stdlib Require Import List Permutation.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Import ListNotations.

(** ** Flat Model (Definition 5.2) *)

Definition FlatModel := FiniteSet VersionedQuad.

Definition in_flat_model (vq : VersionedQuad) (fm : FlatModel) : Prop :=
  In vq fm.

Definition flat_model_versions (fm : FlatModel) : VersionSet :=
  map vq_version fm.

(** ** Condensed Model (Definition 5.4) *)

(** The condensed model is a partial function from quads to version sets,
    represented as an association list. *)
Definition CondensedModel := list (Quad * VersionSet).

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

Definition condensed_domain (cm : CondensedModel) : list Quad :=
  map fst cm.

(** ** Condensation (Definition 5.5) *)

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

(** Quads of a flat model (one entry per versioned quad; duplicates are
    harmless for [models_correspond], see [condense_flatten_identity]). *)
Definition unique_quads (fm : FlatModel) : list Quad :=
  map versioned_quad_to_quad fm.

(** C(q) = { v | (s, p, o, g, v) ∈ d_F } *)
Definition condense (fm : FlatModel) : CondensedModel :=
  map (fun q => (q, versions_of_quad q fm)) (unique_quads fm).

(** ** Flattening (Definition 5.6) *)

(** F(d_C) = { (s, p, o, g, v) | v ∈ d_C(s, p, o, g) } *)
Definition flatten (cm : CondensedModel) : FlatModel :=
  flat_map (fun qvs : Quad * VersionSet =>
    map (fun v => quad_with_version (fst qvs) v) (snd qvs)
  ) cm.

(** ** Model Correspondence *)

(** Two models correspond if they represent the same versioned quads. *)
Definition models_correspond (fm : FlatModel) (cm : CondensedModel) : Prop :=
  forall vq : VersionedQuad,
    in_flat_model vq fm <->
    exists vs, condensed_lookup (versioned_quad_to_quad vq) cm = Some vs /\
               In (vq_version vq) vs.

(** ** Auxiliary Lemmas *)

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

Lemma versioned_quad_to_quad_components : forall vq,
  quad_subject (versioned_quad_to_quad vq) = vq_subject vq /\
  quad_predicate (versioned_quad_to_quad vq) = vq_predicate vq /\
  quad_object (versioned_quad_to_quad vq) = vq_object vq /\
  quad_graph (versioned_quad_to_quad vq) = vq_graph vq.
Proof.
  intros vq. destruct vq. simpl. auto.
Qed.

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

Lemma condensed_lookup_cons_neq : forall q q' vs rest,
  q <> q' ->
  condensed_lookup q ((q', vs) :: rest) = condensed_lookup q rest.
Proof.
  intros [s p o g] [s' p' o' g'] vs rest Hneq. simpl.
  destruct (IRI_eq_dec s s'); [|reflexivity].
  destruct (IRI_eq_dec p p'); [|reflexivity].
  destruct (Term_eq_dec o o'); [|reflexivity].
  destruct (IRI_eq_dec g g'); [|reflexivity].
  subst. contradiction.
Qed.

Lemma condensed_lookup_in_map_eq : forall q qs (f : Quad -> VersionSet),
  In q qs ->
  condensed_lookup q (map (fun q' => (q', f q')) qs) = Some (f q).
Proof.
  intros q qs f Hin.
  induction qs as [|q' rest IH].
  - contradiction.
  - cbn [map]. destruct (Quad_eq_dec q q') as [Heq|Hneq].
    + subst q'. apply condensed_lookup_cons_eq.
    + rewrite condensed_lookup_cons_neq by exact Hneq.
      apply IH. destruct Hin as [Heq | Hin];
        [subst; exfalso; apply Hneq; reflexivity | exact Hin].
Qed.

Lemma condensed_lookup_in_map_result : forall q qs (f : Quad -> VersionSet) vs,
  condensed_lookup q (map (fun q' => (q', f q')) qs) = Some vs ->
  vs = f q.
Proof.
  intros q qs f vs H.
  induction qs as [|q' rest IH].
  - simpl in H. discriminate.
  - cbn [map] in H. destruct (Quad_eq_dec q q') as [Heq|Hneq].
    + subst q'. rewrite condensed_lookup_cons_eq in H. congruence.
    + rewrite condensed_lookup_cons_neq in H by exact Hneq. auto.
Qed.

Lemma condensed_lookup_Some_In : forall q vs cm,
  condensed_lookup q cm = Some vs ->
  In (q, vs) cm.
Proof.
  intros q vs cm H.
  induction cm as [|[q' vs'] rest IH].
  - simpl in H. discriminate.
  - destruct (Quad_eq_dec q q') as [Heq|Hneq].
    + subst q'. rewrite condensed_lookup_cons_eq in H. left. congruence.
    + rewrite condensed_lookup_cons_neq in H by exact Hneq. right. auto.
Qed.

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

(** ** Theorem 6.1: Inverse Properties (set-theoretic form) *)

(** F ∘ C (d_F) represents d_F. *)
Theorem condense_flatten_identity : forall fm : FlatModel,
  models_correspond fm (condense fm).
Proof.
  intros fm.
  unfold models_correspond, in_flat_model.
  intros vq. split.
  - intro Hin. apply condensed_lookup_in_condense. exact Hin.
  - intros [vs [Hlookup Hversion_in]].
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

(** ** Well-formedness of Condensed Models *)

(** A condensed model is well-formed when it is a genuine partial function
    (no quad appears twice as a key) and every version set is a non-empty
    set (duplicate-free).  Non-emptiness reflects that [D(d_C)] only
    contains quads valid in at least one version (Definition 5.5). *)
Definition wf_condensed (cm : CondensedModel) : Prop :=
  NoDup (map fst cm).

Definition wf_condensed_model (cm : CondensedModel) : Prop :=
  NoDup (map fst cm) /\
  Forall (fun qvs : Quad * VersionSet => NoDup (snd qvs) /\ snd qvs <> []) cm.

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
      destruct (Quad_eq_dec q q') as [Heq|Hneq].
      * subst q'. exfalso. apply Hnotin.
        apply in_map_iff. exists (q, vs). auto.
      * rewrite condensed_lookup_cons_neq by exact Hneq. auto.
Qed.

(** Under [NoDup] keys, a key determines its entry. *)
Lemma NoDup_fst_unique {A B : Type} (l : list (A * B)) a b b' :
  NoDup (map fst l) -> In (a, b) l -> In (a, b') l -> b = b'.
Proof.
  induction l as [|[a0 b0] l IH]; simpl; intros Hnd H1 H2; [contradiction|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  destruct H1 as [H1 | H1]; destruct H2 as [H2 | H2].
  - congruence.
  - inversion H1; subst. exfalso. apply Hnotin.
    apply in_map_iff. exists (a, b'). auto.
  - inversion H2; subst. exfalso. apply Hnotin.
    apply in_map_iff. exists (a, b). auto.
  - auto.
Qed.

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

(** C ∘ F (d_C) represents d_C (under well-formedness). *)
Theorem flatten_condense_identity : forall cm : CondensedModel,
  wf_condensed cm ->
  models_correspond (flatten cm) cm.
Proof.
  intros cm Hwf.
  unfold models_correspond, in_flat_model.
  intros vq. split.
  - intro Hin.
    apply in_flatten_inv in Hin.
    destruct Hin as [q [vs [Hqvs [Hvq [Hquad Hvin]]]]].
    exists vs. split.
    + rewrite Hquad.
      apply condensed_lookup_NoDup; [exact Hwf | exact Hqvs].
    + exact Hvin.
  - intros [vs [Hlookup Hversion]].
    apply condensed_lookup_Some_In in Hlookup.
    rewrite <- (quad_with_version_inverse vq).
    eapply in_flatten; eassumption.
Qed.

(** ** Named Graphs of an Archive *)

(** The (graph, version) pairs present in a flat model, without
    duplicates: the named graphs of the flat dataset, seen as versioned
    IRIs, are exactly [VI(v, g)] for these pairs. *)
Definition GraphVersion_eq_dec :
  forall a b : IRI * Version, {a = b} + {a <> b}.
Proof.
  intros [g v] [g' v'].
  destruct (IRI_eq_dec g g'); destruct (Version_eq_dec v v');
    [left; congruence | right; congruence | right; congruence | right; congruence].
Defined.

Definition flat_graphs (fm : FlatModel) : list (IRI * Version) :=
  nodup GraphVersion_eq_dec (map (fun vq => (vq_graph vq, vq_version vq)) fm).

Lemma in_flat_graphs : forall fm g v,
  In (g, v) (flat_graphs fm) <->
  exists vq, In vq fm /\ vq_graph vq = g /\ vq_version vq = v.
Proof.
  intros fm g v. unfold flat_graphs. rewrite nodup_In, in_map_iff. split.
  - intros [vq [Heq Hin]]. injection Heq as <- <-. eauto.
  - intros [vq [Hin [<- <-]]]. eauto.
Qed.

Lemma NoDup_flat_graphs : forall fm, NoDup (flat_graphs fm).
Proof. intros fm. apply NoDup_nodup. Qed.

(** The catalog of a condensed model: each named graph with the set of
    versions in which it holds at least one quad. *)
Definition graph_versions (g : IRI) (cm : CondensedModel) : VersionSet :=
  nodup Version_eq_dec
    (flat_map (fun qvs : Quad * VersionSet =>
                 if IRI_eq_dec (quad_graph (fst qvs)) g then snd qvs else []) cm).

Definition graph_catalog (cm : CondensedModel) : Catalog :=
  map (fun g => (g, graph_versions g cm))
      (nodup IRI_eq_dec (map (fun qvs : Quad * VersionSet => quad_graph (fst qvs)) cm)).

Lemma in_graph_versions : forall g cm v,
  In v (graph_versions g cm) <->
  exists q vs, In (q, vs) cm /\ quad_graph q = g /\ In v vs.
Proof.
  intros g cm v. unfold graph_versions. rewrite nodup_In, in_flat_map. split.
  - intros [[q vs] [Hin Hv]]. cbn [fst snd] in Hv.
    destruct (IRI_eq_dec (quad_graph q) g) as [<- | Hneq]; [eauto | contradiction].
  - intros [q [vs [Hin [<- Hv]]]]. exists (q, vs). split; [exact Hin|].
    cbn [fst snd]. destruct (IRI_eq_dec (quad_graph q) (quad_graph q));
      [exact Hv | contradiction].
Qed.

Lemma in_graph_catalog : forall cm g vs,
  In (g, vs) (graph_catalog cm) <->
  vs = graph_versions g cm /\ exists q vs', In (q, vs') cm /\ quad_graph q = g.
Proof.
  intros cm g vs. unfold graph_catalog. rewrite in_map_iff. split.
  - intros [g' [Heq Hin]]. injection Heq as <- <-. split; [reflexivity|].
    rewrite nodup_In, in_map_iff in Hin. destruct Hin as [[q vs'] [<- Hin]].
    exists q, vs'. auto.
  - intros [-> [q [vs' [Hin Hg]]]]. exists g. split; [reflexivity|].
    rewrite nodup_In, in_map_iff. exists (q, vs'). auto.
Qed.

(** The pairs of the catalog are the pairs of the flattening. *)
Lemma in_catalog_pairs_graph_catalog : forall cm g v,
  In (g, v) (catalog_pairs (graph_catalog cm)) <->
  exists q vs, In (q, vs) cm /\ quad_graph q = g /\ In v vs.
Proof.
  intros cm g v. rewrite in_catalog_pairs. split.
  - intros [vs [Hin Hv]]. apply in_graph_catalog in Hin.
    destruct Hin as [-> _]. apply in_graph_versions. exact Hv.
  - intros H. exists (graph_versions g cm). split.
    + apply in_graph_catalog. split; [reflexivity|].
      destruct H as [q [vs [Hin [Hg _]]]]. eauto.
    + apply in_graph_versions. exact H.
Qed.

Lemma graph_catalog_NoDup : forall cm,
  NoDup (map fst (graph_catalog cm)) /\
  Forall (fun gv : IRI * VersionSet => NoDup (snd gv)) (graph_catalog cm).
Proof.
  intros cm. split.
  - unfold graph_catalog. rewrite map_map. cbn [fst].
    rewrite map_id. apply NoDup_nodup.
  - apply Forall_forall. intros [g vs] Hin. apply in_graph_catalog in Hin.
    destruct Hin as [-> _]. apply NoDup_nodup.
Qed.

Lemma wf_catalog_graph_catalog : forall cm,
  wf_condensed_model cm -> graph_catalog cm <> [] ->
  wf_catalog (graph_catalog cm).
Proof.
  intros cm [_ Hwf] Hne. split; [|split; [|exact Hne]].
  - apply graph_catalog_NoDup.
  - apply Forall_forall. intros [g vs] Hin. apply in_graph_catalog in Hin.
    destruct Hin as [-> [q [vs' [Hin Hg]]]]. cbn [snd]. split.
    + apply NoDup_nodup.
    + rewrite Forall_forall in Hwf. specialize (Hwf _ Hin). cbn [snd] in Hwf.
      destruct Hwf as [_ Hne']. destruct vs' as [|v vs']; [contradiction|].
      intros H. assert (In v (graph_versions g cm)) as Hv.
      { apply in_graph_versions. exists q, (v :: vs'). split; [exact Hin|].
        split; [exact Hg | left; reflexivity]. }
      rewrite H in Hv. contradiction.
Qed.

(** ** From Correspondence to Permutation *)

(** The flattening of a well-formed condensed model has no duplicates. *)
Lemma NoDup_flatten : forall cm,
  wf_condensed_model cm -> NoDup (flatten cm).
Proof.
  intros cm [Hkeys Hvs]. unfold flatten.
  apply NoDup_flat_map.
  - eapply NoDup_map_inv. exact Hkeys.
  - intros [q vs] Hin. simpl.
    rewrite Forall_forall in Hvs. specialize (Hvs _ Hin). simpl in Hvs.
    apply NoDup_map_inj_in; [|tauto].
    intros v v' _ _ Heq.
    apply (f_equal vq_version) in Heq.
    rewrite !quad_with_version_version in Heq. exact Heq.
  - intros [q vs] [q' vs'] vq Hin Hin' Hvq Hvq'. simpl in *.
    apply in_map_iff in Hvq. destruct Hvq as [v [Hv _]].
    apply in_map_iff in Hvq'. destruct Hvq' as [v' [Hv' _]].
    assert (q = q').
    { rewrite <- (quad_with_version_to_quad q v), Hv, <- Hv'.
      apply quad_with_version_to_quad. }
    subst q'. f_equal. eapply NoDup_fst_unique; eauto.
Qed.

(** A duplicate-free flat model corresponding to a well-formed condensed
    model is, up to order, exactly its flattening.  This is the bag-semantics
    form of Theorem 6.1 used by the evaluation equivalence theorem. *)
Theorem models_correspond_Permutation : forall fm cm,
  wf_condensed_model cm ->
  NoDup fm ->
  models_correspond fm cm ->
  Permutation fm (flatten cm).
Proof.
  intros fm cm Hwf Hnd Hcorr.
  apply NoDup_Permutation; [exact Hnd | apply NoDup_flatten; exact Hwf |].
  intros vq. rewrite (Hcorr vq). split.
  - intros [vs [Hlookup Hv]].
    apply condensed_lookup_Some_In in Hlookup.
    rewrite <- (quad_with_version_inverse vq).
    eapply in_flatten; eassumption.
  - intros Hin. apply in_flatten_inv in Hin.
    destruct Hin as [q [vs [Hqvs [_ [Hquad Hvin]]]]].
    exists vs. rewrite Hquad. split; [|exact Hvin].
    apply condensed_lookup_NoDup; [apply Hwf | exact Hqvs].
Qed.

(** The named graphs of corresponding models coincide. *)
Lemma flat_graphs_catalog_pairs : forall fm cm g v,
  Permutation fm (flatten cm) ->
  In (g, v) (flat_graphs fm) <-> In (g, v) (catalog_pairs (graph_catalog cm)).
Proof.
  intros fm cm g v HP. rewrite in_flat_graphs, in_catalog_pairs_graph_catalog.
  split.
  - intros [vq [Hin [<- <-]]].
    apply (Permutation_in _ HP) in Hin. apply in_flatten_inv in Hin.
    destruct Hin as [q [vs [Hqvs [_ [Hq Hv]]]]]. exists q, vs.
    split; [exact Hqvs|]. split; [|exact Hv].
    rewrite <- Hq. destruct vq. reflexivity.
  - intros [q [vs [Hin [<- Hv]]]]. exists (quad_with_version q v).
    split; [|split; destruct q; reflexivity].
    apply (Permutation_in _ (Permutation_sym HP)).
    apply in_flatten with (vs := vs); assumption.
Qed.
