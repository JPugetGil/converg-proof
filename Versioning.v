(** * Versioning: Versions, Versioned IRIs and Versioned Quads

    Thesis, Chapter 3 (Section 3.4) and Chapter 5 (Definition 5.1).

    A versioned IRI [VI(v, g)] identifies the named graph [g] at snapshot
    [v].  Following the thesis, versioned IRIs form a subset [VI ⊂ I] of
    the IRIs, so that the graph variable of a flat solution mapping can be
    bound to the RDF term [TermIRI (vi v g)].
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Import ListNotations.

(** ** Versions *)

(** A version identifies a snapshot of the archive. *)
Parameter Version : Type.
Parameter Version_eq_dec : forall v1 v2 : Version, {v1 = v2} + {v1 <> v2}.

(** A version set is a finite set of versions, represented as a list.
    Well-formed version sets are duplicate-free (see [wf_version_set]). *)
Definition VersionSet := FiniteSet Version.

(** ** Versioned IRIs (Definition 5.1) *)

(** The injective function [VI : V × I → VI ⊆ I]. *)
Parameter vi : Version -> IRI -> IRI.

(** Modeling assumption: [VI] is injective (it is a bijection onto its
    image [VI]). *)
Axiom vi_injective : forall v1 v2 g1 g2,
  vi v1 g1 = vi v2 g2 -> v1 = v2 /\ g1 = g2.

(** The inverse functions of Equation (5.1), defined on the image of [vi]. *)
Parameter vi_inv_version : IRI -> Version.
Parameter vi_inv_graph : IRI -> IRI.

Axiom vi_inv_version_correct : forall v g, vi_inv_version (vi v g) = v.
Axiom vi_inv_graph_correct : forall v g, vi_inv_graph (vi v g) = g.

(** ** Versioned Quads (Definition 3.1) *)

Record VersionedQuad : Type := mkVersionedQuad {
  vq_subject : IRI;
  vq_predicate : IRI;
  vq_object : Term;
  vq_graph : IRI;
  vq_version : Version
}.

Definition versioned_quad_to_quad (vq : VersionedQuad) : Quad :=
  mkQuad (vq_subject vq) (vq_predicate vq) (vq_object vq) (vq_graph vq).

Definition versioned_quad_version (vq : VersionedQuad) : Version :=
  vq_version vq.

Definition quad_with_version (q : Quad) (v : Version) : VersionedQuad :=
  mkVersionedQuad (quad_subject q) (quad_predicate q) (quad_object q)
                  (quad_graph q) v.

(** ** Version Set Operations *)

Definition version_set_empty : VersionSet := [].

Definition version_set_singleton (v : Version) : VersionSet := [v].

Definition version_set_union (vs1 vs2 : VersionSet) : VersionSet :=
  vs1 ++ vs2.

(** Intersection keeps the elements of [vs1] that also belong to [vs2];
    it therefore preserves [NoDup vs1]. *)
Definition version_set_intersection (vs1 vs2 : VersionSet) : VersionSet :=
  filter (fun v => inb Version_eq_dec v vs2) vs1.

(** Difference: elements of [vs1] that are not in [vs2]. *)
Definition version_set_diff (vs1 vs2 : VersionSet) : VersionSet :=
  filter (fun v => negb (inb Version_eq_dec v vs2)) vs1.

Definition version_set_nonempty (vs : VersionSet) : Prop := vs <> [].

Definition version_set_card (vs : VersionSet) : nat := length vs.

(** A well-formed version set has no duplicates. *)
Definition wf_version_set (vs : VersionSet) : Prop := NoDup vs.

(** ** Lemmas *)

Lemma version_set_intersection_In vs1 vs2 v :
  In v (version_set_intersection vs1 vs2) <-> In v vs1 /\ In v vs2.
Proof.
  unfold version_set_intersection. rewrite filter_In, inb_true_iff. tauto.
Qed.

Lemma version_set_diff_In vs1 vs2 v :
  In v (version_set_diff vs1 vs2) <-> In v vs1 /\ ~ In v vs2.
Proof.
  unfold version_set_diff. rewrite filter_In, negb_true_iff, inb_false_iff.
  tauto.
Qed.

Lemma NoDup_version_set_intersection vs1 vs2 :
  NoDup vs1 -> NoDup (version_set_intersection vs1 vs2).
Proof. apply NoDup_filter. Qed.

Lemma NoDup_version_set_diff vs1 vs2 :
  NoDup vs1 -> NoDup (version_set_diff vs1 vs2).
Proof. apply NoDup_filter. Qed.

(** The versioned IRIs of a duplicate-free version set are pairwise
    distinct (injectivity of [vi] in its first argument). *)
Lemma NoDup_map_vi (g : IRI) (vs : VersionSet) :
  NoDup vs -> NoDup (map (fun v => vi v g) vs).
Proof.
  intros H. apply NoDup_map_inj_in; auto.
  intros v v' _ _ Heq. apply vi_injective in Heq. tauto.
Qed.

Lemma in_map_vi (g g' : IRI) (v : Version) (vs : VersionSet) :
  In (vi v g) (map (fun v' => vi v' g') vs) <-> g = g' /\ In v vs.
Proof.
  rewrite in_map_iff. split.
  - intros [v' [Heq Hv']]. apply vi_injective in Heq.
    destruct Heq; subst. auto.
  - intros [<- Hv]. exists v. auto.
Qed.
