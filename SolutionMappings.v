(** * SolutionMappings: Flat and Condensed Solution Mappings

    Thesis, Sections 5.2–5.3 (Definitions 5.7, 5.8, 5.20–5.26, 5.39) and
    the preservation lemmas of Chapter 6 (Lemmas 6.3, 6.4, 6.5, 6.6, 6.7).

    A flat solution mapping binds variables to RDF terms (representation ν
    only).  A condensed (typed) solution mapping binds each variable to a
    [Binding] whose representation is ν, ι or ζ.  The expansion function
    [expand] (Ξ, Definition 5.22) turns a condensed mapping into the list
    of flat mappings it represents.

    Both kinds of mappings are association lists; evaluation only produces
    mappings with duplicate-free keys ([wf_cmap]).
*)

From Stdlib Require Import List Permutation Bool PeanoNat Lia.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Import ListNotations.

(** ** Bindings (Definition 5.20) *)

Inductive Binding : Type :=
  | BVal : Term -> Binding                 (** ν: an RDF term *)
  | BId : nat -> Binding                   (** ι: a term identifier *)
  | BCond : IRI -> VersionSet -> Binding.  (** ζ: (named graph, version set) *)

Definition binding_repr (b : Binding) : Representation :=
  match b with
  | BVal _ => Value
  | BId _ => Id
  | BCond _ _ => Condensed
  end.

(** Term-level forms of the injectivity of [vi]. *)
Lemma NoDup_map_term_vi : forall (g : IRI) (vs : VersionSet),
  NoDup vs -> NoDup (map (fun v => TermIRI (vi v g)) vs).
Proof.
  intros g vs H. apply NoDup_map_inj_in; [|exact H].
  intros v v' _ _ Heq. injection Heq as Heq. apply vi_injective in Heq. tauto.
Qed.

Lemma in_map_term_vi : forall (g g' : IRI) (v : Version) (vs : VersionSet),
  In (TermIRI (vi v g)) (map (fun v' => TermIRI (vi v' g')) vs) <->
  g = g' /\ In v vs.
Proof.
  intros g g' v vs. rewrite in_map_iff. split.
  - intros [v' [Heq Hv']]. injection Heq as Heq. apply vi_injective in Heq.
    destruct Heq; subst. auto.
  - intros [<- Hv]. exists v. auto.
Qed.

(** ** Represented Values (Definition 5.21) *)

(** vals(b): the RDF terms denoted by a binding.  For a ζ binding (g, V),
    these are the versioned IRIs VI(v, g) for v ∈ V. *)
Definition vals (b : Binding) : list Term :=
  match b with
  | BVal t => [t]
  | BId n => [id_to_val n]
  | BCond g vs => map (fun v => TermIRI (vi v g)) vs
  end.

(** A point-valued binding denotes exactly one term. *)
Definition point_val (b : Binding) : option Term :=
  match b with
  | BVal t => Some t
  | BId n => Some (id_to_val n)
  | BCond _ _ => None
  end.

Lemma point_val_vals : forall b t, point_val b = Some t -> vals b = [t].
Proof. intros b t H; destruct b; simpl in *; congruence. Qed.

Lemma point_val_repr : forall b,
  point_val b <> None <-> point_repr (binding_repr b) = true.
Proof. intros []; simpl; split; intros; congruence. Qed.

(** ** Well-formed Bindings *)

(** A ζ binding carries a non-empty, duplicate-free set of versions. *)
Definition wf_binding (b : Binding) : Prop :=
  match b with
  | BCond _ vs => NoDup vs /\ vs <> []
  | _ => True
  end.

Lemma wf_binding_NoDup_vals : forall b, wf_binding b -> NoDup (vals b).
Proof.
  intros [t | n | g vs]; simpl; intros H.
  - repeat constructor; auto.
  - repeat constructor; auto.
  - apply NoDup_map_term_vi. tauto.
Qed.

Lemma wf_binding_vals_nonempty : forall b, wf_binding b -> vals b <> [].
Proof.
  intros [t | n | g vs]; simpl; intros H; try discriminate.
  destruct vs; [tauto | discriminate].
Qed.

(** ** Mappings and Lookup *)

(** Flat solution mappings: all variables in representation ν. *)
Definition FMapping := list (Var * Term).

(** Condensed (typed) solution mappings (Definition 5.20). *)
Definition CMapping := list (Var * Binding).

Fixpoint lookup {A : Type} (x : Var) (m : list (Var * A)) : option A :=
  match m with
  | [] => None
  | (y, a) :: rest => if Var_eq_dec x y then Some a else lookup x rest
  end.

Definition keys {A : Type} (m : list (Var * A)) : list Var := map fst m.

Definition memb (x : Var) (l : list Var) : bool := inb Var_eq_dec x l.

Lemma lookup_Some_In {A : Type} (x : Var) (m : list (Var * A)) a :
  lookup x m = Some a -> In (x, a) m.
Proof.
  induction m as [|[y a'] rest IH]; simpl; intros H; [discriminate|].
  destruct (Var_eq_dec x y); [left; congruence | right; auto].
Qed.

Lemma lookup_None_iff {A : Type} (x : Var) (m : list (Var * A)) :
  lookup x m = None <-> ~ In x (keys m).
Proof.
  induction m as [|[y a] rest IH]; simpl.
  - tauto.
  - destruct (Var_eq_dec x y) as [-> | Hneq].
    + split; [discriminate | intros H; exfalso; apply H; left; reflexivity].
    + rewrite IH. split.
      * intros H [Heq | Hin]; [congruence | exact (H Hin)].
      * intros H Hin. apply H. right. exact Hin.
Qed.

Lemma lookup_In_keys {A : Type} (x : Var) (m : list (Var * A)) a :
  lookup x m = Some a -> In x (keys m).
Proof.
  intros H. apply lookup_Some_In in H. unfold keys.
  apply in_map_iff. exists (x, a). auto.
Qed.

Lemma In_keys_lookup {A : Type} (x : Var) (m : list (Var * A)) :
  In x (keys m) -> exists a, lookup x m = Some a.
Proof.
  intros H. destruct (lookup x m) eqn:E; [eauto|].
  apply lookup_None_iff in E. contradiction.
Qed.

Lemma in_lookup_NoDup {A : Type} (x : Var) (m : list (Var * A)) a :
  NoDup (keys m) -> In (x, a) m -> lookup x m = Some a.
Proof.
  induction m as [|[y a'] rest IH]; simpl; intros Hnd Hin; [contradiction|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  destruct (Var_eq_dec x y) as [-> | Hneq].
  - destruct Hin as [Hin | Hin]; [congruence|].
    exfalso. apply Hnotin. unfold keys. apply in_map_iff. exists (y, a). auto.
  - destruct Hin as [Hin | Hin]; [congruence | auto].
Qed.

Lemma lookup_app {A : Type} (x : Var) (m1 m2 : list (Var * A)) :
  lookup x (m1 ++ m2) =
  match lookup x m1 with Some a => Some a | None => lookup x m2 end.
Proof.
  induction m1 as [|[y a] rest IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec x y); auto.
Qed.

Lemma lookup_map_fst {A B : Type} (x : Var) (h : Var * A -> B)
      (m : list (Var * A)) :
  lookup x (map (fun ya => (fst ya, h ya)) m) =
  match lookup x m with Some a => Some (h (x, a)) | None => None end.
Proof.
  induction m as [|[y a] rest IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec x y) as [-> | Hneq]; auto.
Qed.

Lemma lookup_filter_keep {A : Type} (x : Var) (p : Var * A -> bool)
      (m : list (Var * A)) :
  (forall a, p (x, a) = true) ->
  lookup x (filter p m) = lookup x m.
Proof.
  intros Hp. induction m as [|[y a] rest IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec x y) as [-> | Hneq].
  - rewrite Hp. simpl. destruct (Var_eq_dec y y); [reflexivity | contradiction].
  - destruct (p (y, a)); simpl; destruct (Var_eq_dec x y);
      try contradiction; auto.
Qed.

Lemma lookup_filter_drop {A : Type} (x : Var) (p : Var * A -> bool)
      (m : list (Var * A)) :
  (forall a, p (x, a) = false) ->
  lookup x (filter p m) = None.
Proof.
  intros Hp. induction m as [|[y a] rest IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec x y) as [-> | Hneq].
  - rewrite Hp. exact IH.
  - destruct (p (y, a)); simpl;
      [destruct (Var_eq_dec x y); [contradiction | exact IH] | exact IH].
Qed.

Lemma keys_app {A : Type} (m1 m2 : list (Var * A)) :
  keys (m1 ++ m2) = keys m1 ++ keys m2.
Proof. unfold keys. apply map_app. Qed.

Lemma keys_map_fst {A B : Type} (h : Var * A -> B) (m : list (Var * A)) :
  keys (map (fun ya => (fst ya, h ya)) m) = keys m.
Proof. unfold keys. rewrite map_map. reflexivity. Qed.

Lemma keys_filter {A : Type} (q : Var * A -> bool) (p : Var -> bool)
      (m : list (Var * A)) :
  (forall xa, q xa = p (fst xa)) ->
  keys (filter q m) = filter p (keys m).
Proof.
  intros Hq. unfold keys. induction m as [|[x a] m IH]; simpl; [reflexivity|].
  rewrite Hq. simpl. destruct (p x); simpl; rewrite IH; reflexivity.
Qed.

Lemma keys_filter_fst {A : Type} (p : Var -> bool) (m : list (Var * A)) :
  keys (filter (fun xa => p (fst xa)) m) = filter p (keys m).
Proof. apply keys_filter. intros; reflexivity. Qed.

Lemma NoDup_keys_filter {A : Type} (p : Var * A -> bool) (m : list (Var * A)) :
  NoDup (keys m) -> NoDup (keys (filter p m)).
Proof.
  unfold keys. induction m as [|[y a] rest IH]; simpl; intros H; [constructor|].
  apply NoDup_cons_iff in H. destruct H as [Hnotin Hnd].
  destruct (p (y, a)); simpl; [|apply IH; exact Hnd].
  constructor; [|apply IH; exact Hnd]. intros Hin. apply Hnotin.
  apply in_map_iff in Hin. destruct Hin as [[y' a'] [Heq Hin]].
  apply filter_In in Hin. apply in_map_iff. exists (y', a'). tauto.
Qed.

(** Two flat mappings with the same (duplicate-free) keys and the same
    lookups are equal. *)
Lemma fmap_ext_eq : forall (f f' : FMapping),
  keys f = keys f' -> NoDup (keys f) ->
  (forall x, lookup x f = lookup x f') -> f = f'.
Proof.
  induction f as [|[x t] f IH]; intros [|[x' t'] f'] Hkeys Hnd Hlk;
    simpl in *; try discriminate; [reflexivity|].
  injection Hkeys as <- Hkeys.
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  pose proof (Hlk x) as Hx. simpl in Hx.
  destruct (Var_eq_dec x x); [|contradiction]. injection Hx as <-.
  f_equal. apply IH; auto.
  intros y. pose proof (Hlk y) as Hy. simpl in Hy.
  destruct (Var_eq_dec y x) as [-> | Hneq]; [|exact Hy].
  assert (E1 : lookup x f = None) by (apply lookup_None_iff; exact Hnotin).
  assert (E2 : lookup x f' = None).
  { apply lookup_None_iff. unfold keys in *. rewrite <- Hkeys. exact Hnotin. }
  rewrite E1, E2. reflexivity.
Qed.

Lemma app_eq_length_prefix {A : Type} : forall (a a' b b' : list A),
  length a = length a' -> a ++ b = a' ++ b' -> a = a' /\ b = b'.
Proof.
  induction a as [|x a IH]; intros [|x' a'] b b' Hlen Heq; simpl in *;
    try discriminate; [auto|].
  injection Heq as <- Heq. injection Hlen as Hlen.
  destruct (IH a' b b' Hlen Heq) as [<- <-]. auto.
Qed.

(** ** Expansion (Definition 5.22) *)

(** Ξ(m): all flat mappings obtained by choosing, for each variable, one of
    the represented values of its binding (in the order of the mapping). *)
Fixpoint expand (m : CMapping) : list FMapping :=
  match m with
  | [] => [[]]
  | (x, b) :: m' =>
      flat_map (fun t => map (fun f => (x, t) :: f) (expand m')) (vals b)
  end.

(** Position-wise characterization of membership in an expansion. *)
Definition ExpandRel (xt : Var * Term) (xb : Var * Binding) : Prop :=
  fst xt = fst xb /\ In (snd xt) (vals (snd xb)).

Lemma in_expand : forall m f,
  In f (expand m) <-> Forall2 ExpandRel f m.
Proof.
  induction m as [|[x b] m IH]; intros f; simpl.
  - split.
    + intros [<- | []]. constructor.
    + intros H. inversion H; subst. left. reflexivity.
  - rewrite in_flat_map. split.
    + intros [t [Ht Hf]]. apply in_map_iff in Hf.
      destruct Hf as [f' [<- Hf']]. constructor.
      * split; simpl; auto.
      * apply IH. exact Hf'.
    + intros H. inversion H as [| xt xb f' m' Hrel Hrest]; subst.
      destruct xt as [x' t]. destruct Hrel as [Heq Hvals]. simpl in Heq, Hvals.
      subst x'. exists t. split; [exact Hvals|].
      apply in_map_iff. exists f'. split; [reflexivity | apply IH; exact Hrest].
Qed.

Lemma expand_keys : forall m f, In f (expand m) -> keys f = keys m.
Proof.
  intros m f H. apply in_expand in H. unfold keys.
  induction H as [| xt xb f m [Heq _] _ IH]; simpl; [reflexivity|].
  rewrite Heq, IH. reflexivity.
Qed.

Lemma expand_lookup : forall m f x t,
  In f (expand m) -> lookup x f = Some t ->
  exists b, lookup x m = Some b /\ In t (vals b).
Proof.
  intros m f x t H. apply in_expand in H.
  induction H as [| [y t'] [y' b'] f m [Heq Hvals] _ IH]; simpl; intros Hl;
    [discriminate|].
  simpl in Heq, Hvals. subst y'.
  destruct (Var_eq_dec x y).
  - injection Hl as <-. exists b'. auto.
  - auto.
Qed.

Lemma expand_lookup_None : forall m f x,
  In f (expand m) -> (lookup x f = None <-> lookup x m = None).
Proof.
  intros m f x H. rewrite !lookup_None_iff. rewrite (expand_keys m f H). tauto.
Qed.

Lemma expand_lookup_point : forall m f x b t,
  In f (expand m) -> lookup x m = Some b -> point_val b = Some t ->
  lookup x f = Some t.
Proof.
  intros m f x b t Hf Hb Hp.
  destruct (lookup x f) as [t'|] eqn:E.
  - destruct (expand_lookup m f x t' Hf E) as [b' [Hb' Ht']].
    rewrite Hb in Hb'. injection Hb' as <-.
    rewrite (point_val_vals b t Hp) in Ht'. destruct Ht' as [<- | []].
    reflexivity.
  - rewrite expand_lookup_None in E by exact Hf. congruence.
Qed.

Lemma expand_app_in : forall m1 m2 f1 f2,
  In f1 (expand m1) -> In f2 (expand m2) -> In (f1 ++ f2) (expand (m1 ++ m2)).
Proof.
  intros m1 m2 f1 f2 H1 H2. apply in_expand. apply Forall2_app; apply in_expand;
    assumption.
Qed.

Lemma expand_app_inv : forall m1 m2 f,
  In f (expand (m1 ++ m2)) ->
  exists f1 f2, f = f1 ++ f2 /\ In f1 (expand m1) /\ In f2 (expand m2).
Proof.
  intros m1 m2 f H. apply in_expand in H.
  apply Forall2_app_inv_r in H. destruct H as [f1 [f2 [H1 [H2 ->]]]].
  exists f1, f2. repeat split; apply in_expand; assumption.
Qed.

Lemma expand_filter_keys : forall m f (p : Var -> bool),
  In f (expand m) ->
  In (filter (fun xt => p (fst xt)) f) (expand (filter (fun xb => p (fst xb)) m)).
Proof.
  intros m f p H. apply in_expand in H. apply in_expand.
  induction H as [| [y t] [y' b] f m [Heq Hvals] _ IH]; simpl; [constructor|].
  simpl in Heq, Hvals. subst y'.
  destruct (p y); [constructor; [split; auto | exact IH] | exact IH].
Qed.

(** The expansion of a mapping with duplicate-free bindings has no
    duplicates. *)
Lemma NoDup_expand : forall m,
  Forall (fun xb => NoDup (vals (snd xb))) m -> NoDup (expand m).
Proof.
  induction m as [|[x b] m IH]; simpl; intros H; [repeat constructor; auto|].
  inversion H as [| ? ? Hb Hm]; subst. simpl in Hb.
  apply NoDup_flat_map; [exact Hb | |].
  - intros t _. apply NoDup_map_inj_in; [|apply IH; exact Hm].
    intros f f' _ _ Heq. injection Heq. auto.
  - intros t t' f _ _ Hf Hf'.
    apply in_map_iff in Hf. destruct Hf as [f1 [<- _]].
    apply in_map_iff in Hf'. destruct Hf' as [f2 [Heq _]].
    injection Heq. auto.
Qed.

(** A mapping whose bindings all denote at least one value has at least one
    expansion. *)
Definition default_term : Term := id_to_val 0.

Definition witness_flat (m : CMapping) : FMapping :=
  map (fun xb => (fst xb, hd default_term (vals (snd xb)))) m.

Lemma witness_flat_in_expand : forall m,
  Forall (fun xb => vals (snd xb) <> []) m ->
  In (witness_flat m) (expand m).
Proof.
  intros m H. apply in_expand. induction m as [|[x b] m IH]; simpl; [constructor|].
  inversion H as [| ? ? Hb Hm]; subst. simpl in Hb.
  constructor; [|apply IH; exact Hm].
  split; simpl; [reflexivity|].
  destruct (vals b) eqn:E; [exfalso; apply Hb; reflexivity | left; reflexivity].
Qed.

(** ** Cardinality (Definition 5.39, Lemma 6.7) *)

(** card(m) = Π_{x} |vals(m(x))|: point-valued variables contribute 1 and
    ζ variables contribute the size of their version set. *)
Definition cardinality (m : CMapping) : nat :=
  fold_right (fun xb n => length (vals (snd xb)) * n) 1 m.

(** Lemma 6.7 (Multiplicative Cardinality): |Ξ(m)| = card(m). *)
Lemma expand_length : forall m, length (expand m) = cardinality m.
Proof.
  induction m as [|[x b] m IH]; simpl; [reflexivity|].
  rewrite length_flat_map_sum. rewrite <- IH.
  induction (vals b) as [|t ts IHts]; simpl; [reflexivity|].
  rewrite length_map, IHts. reflexivity.
Qed.

(** ** Well-formed Condensed Mappings *)

Definition wf_cmap (m : CMapping) : Prop :=
  NoDup (keys m) /\ Forall (fun xb => wf_binding (snd xb)) m.

Lemma wf_cmap_NoDup_vals : forall m,
  wf_cmap m -> Forall (fun xb => NoDup (vals (snd xb))) m.
Proof.
  intros m [_ H]. eapply Forall_impl; [|exact H].
  intros xb. apply wf_binding_NoDup_vals.
Qed.

Lemma wf_cmap_vals_nonempty : forall m,
  wf_cmap m -> Forall (fun xb => vals (snd xb) <> []) m.
Proof.
  intros m [_ H]. eapply Forall_impl; [|exact H].
  intros xb. apply wf_binding_vals_nonempty.
Qed.

Lemma wf_cmap_NoDup_expand : forall m, wf_cmap m -> NoDup (expand m).
Proof. intros m H. apply NoDup_expand, wf_cmap_NoDup_vals. exact H. Qed.

Lemma wf_cmap_lookup : forall m x b,
  wf_cmap m -> lookup x m = Some b -> wf_binding b.
Proof.
  intros m x b [_ H] Hl. apply lookup_Some_In in Hl.
  rewrite Forall_forall in H. apply (H _ Hl).
Qed.

(** Point-valued variables of a mapping. *)
Definition point_on (xs : list Var) (m : CMapping) : Prop :=
  forall x b, In x xs -> lookup x m = Some b -> point_val b <> None.

(** The lookup of a condensed mapping as a partial function to terms
    (defined on point-valued variables only). *)
Definition lk_c (m : CMapping) (x : Var) : option Term :=
  match lookup x m with
  | Some b => point_val b
  | None => None
  end.

Definition lk_f (f : FMapping) (x : Var) : option Term := lookup x f.

(** Lemma 6.3 (Value Preservation): on point-valued variables, a condensed
    mapping and any of its expansions agree. *)
Lemma value_preservation : forall m f x,
  In f (expand m) ->
  (forall b, lookup x m = Some b -> point_val b <> None) ->
  lk_f f x = lk_c m x.
Proof.
  intros m f x Hf Hp. unfold lk_f, lk_c.
  destruct (lookup x m) as [b|] eqn:E.
  - destruct (point_val b) as [t|] eqn:Ep.
    + eapply expand_lookup_point; eauto.
    + exfalso. apply (Hp b); auto.
  - apply (expand_lookup_None m f x Hf). exact E.
Qed.

(** ** Merging Bindings (Definitions 5.25 and 5.26, per variable) *)

(** [merge_binding b1 b2] is the binding representing vals(b1) ∩ vals(b2),
    or [None] when the intersection is empty (incompatible bindings).
    On two ζ bindings this is Definition 5.26 (same named graph, version
    sets intersected); on two point-valued bindings it is the equality test
    of Definition 5.25.  Mixed representations are handled through [vals]
    so that the operation is total. *)
Definition merge_binding (b1 b2 : Binding) : option Binding :=
  match point_val b1 with
  | Some t1 => if in_dec Term_eq_dec t1 (vals b2) then Some b1 else None
  | None =>
    match point_val b2 with
    | Some t2 => if in_dec Term_eq_dec t2 (vals b1) then Some b2 else None
    | None =>
      match b1, b2 with
      | BCond g1 vs1, BCond g2 vs2 =>
          if IRI_eq_dec g1 g2 then
            match version_set_intersection vs1 vs2 with
            | [] => None
            | _ :: _ => Some (BCond g1 (version_set_intersection vs1 vs2))
            end
          else None
      | _, _ => None
      end
    end
  end.

Definition in_vals (b : Binding) (t : Term) : bool := inb Term_eq_dec t (vals b).

Lemma filter_in_vals_singleton : forall (l : list Term) t,
  NoDup l -> In t l ->
  filter (fun t' => inb Term_eq_dec t' [t]) l = [t].
Proof.
  induction l as [|a l IH]; simpl; intros t Hnd Hin; [contradiction|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  destruct Hin as [<- | Hin].
  - unfold inb at 1. destruct (in_dec Term_eq_dec a [a]) as [_|Hn];
      [|exfalso; apply Hn; left; reflexivity].
    f_equal. apply filter_false_In. intros a' Ha'.
    apply inb_false_iff. intros [<- | []]. contradiction.
  - unfold inb at 1. destruct (in_dec Term_eq_dec a [t]) as [[<- | []]|_];
      [contradiction | apply IH; auto].
Qed.

(** Specification of merging: the merged binding represents exactly the
    common values, listed in the order of [vals b1]. *)
Lemma merge_binding_vals : forall b1 b2 b,
  NoDup (vals b1) ->
  merge_binding b1 b2 = Some b ->
  vals b = filter (in_vals b2) (vals b1).
Proof.
  intros b1 b2 b Hnd H. unfold merge_binding in H. unfold in_vals.
  destruct (point_val b1) as [t1|] eqn:E1.
  - destruct (in_dec Term_eq_dec t1 (vals b2)) as [Hin|Hin]; [|discriminate].
    injection H as <-. rewrite (point_val_vals _ _ E1). simpl.
    apply (inb_true_iff Term_eq_dec) in Hin. rewrite Hin. reflexivity.
  - destruct (point_val b2) as [t2|] eqn:E2.
    + destruct (in_dec Term_eq_dec t2 (vals b1)) as [Hin|Hin]; [|discriminate].
      injection H as <-. rewrite (point_val_vals _ _ E2).
      symmetry. apply filter_in_vals_singleton; assumption.
    + destruct b1 as [| | g1 vs1]; try discriminate.
      destruct b2 as [| | g2 vs2]; try discriminate.
      destruct (IRI_eq_dec g1 g2) as [<- | Hneq]; [|discriminate].
      destruct (version_set_intersection vs1 vs2) eqn:Ei; [discriminate|].
      injection H as <-. rewrite <- Ei. cbn [vals].
      unfold version_set_intersection. rewrite filter_map_swap.
      f_equal. apply filter_ext_In. intros w _.
      apply eq_true_iff_eq. rewrite !inb_true_iff. rewrite in_map_term_vi.
      tauto.
Qed.

Lemma merge_binding_None : forall b1 b2,
  merge_binding b1 b2 = None ->
  filter (in_vals b2) (vals b1) = [].
Proof.
  intros b1 b2 H. unfold merge_binding in H. unfold in_vals.
  destruct (point_val b1) as [t1|] eqn:E1.
  - rewrite (point_val_vals _ _ E1).
    destruct (in_dec Term_eq_dec t1 (vals b2)) as [Hin|Hin]; [discriminate|].
    simpl. apply (inb_false_iff Term_eq_dec) in Hin. rewrite Hin. reflexivity.
  - destruct (point_val b2) as [t2|] eqn:E2.
    + destruct (in_dec Term_eq_dec t2 (vals b1)) as [Hin|Hin]; [discriminate|].
      rewrite (point_val_vals _ _ E2). apply filter_false_In.
      intros t Ht. apply inb_false_iff. intros [<- | []]. contradiction.
    + destruct b1 as [| | g1 vs1]; try discriminate.
      destruct b2 as [| | g2 vs2]; try discriminate.
      cbn [vals]. rewrite filter_map_swap.
      destruct (IRI_eq_dec g1 g2) as [<- | Hneq].
      * destruct (version_set_intersection vs1 vs2) eqn:Ei; [|discriminate].
        unfold version_set_intersection in Ei.
        rewrite (filter_ext_In _ (fun v => inb Version_eq_dec v vs2));
          [rewrite Ei; reflexivity|].
        intros v _. apply eq_true_iff_eq. rewrite !inb_true_iff.
        rewrite in_map_term_vi. tauto.
      * rewrite filter_false_In; [reflexivity|]. intros v _.
        apply inb_false_iff. rewrite in_map_term_vi. tauto.
Qed.

Lemma merge_binding_common : forall b1 b2 t,
  In t (vals b1) -> In t (vals b2) ->
  exists b, merge_binding b1 b2 = Some b.
Proof.
  intros b1 b2 t H1 H2.
  destruct (merge_binding b1 b2) as [b|] eqn:E; [eauto|].
  apply merge_binding_None in E.
  assert (In t (filter (in_vals b2) (vals b1))) as Hin.
  { apply filter_In. split; [exact H1|]. unfold in_vals. apply inb_true_iff.
    exact H2. }
  rewrite E in Hin. contradiction.
Qed.

Lemma merge_binding_wf : forall b1 b2 b,
  wf_binding b1 -> wf_binding b2 -> merge_binding b1 b2 = Some b ->
  wf_binding b.
Proof.
  intros b1 b2 b H1 H2 H. unfold merge_binding in H.
  destruct (point_val b1) as [t1|] eqn:E1.
  - destruct (in_dec Term_eq_dec t1 (vals b2)); [congruence | discriminate].
  - destruct (point_val b2) as [t2|] eqn:E2.
    + destruct (in_dec Term_eq_dec t2 (vals b1)); [congruence | discriminate].
    + destruct b1 as [| | g1 vs1]; try discriminate.
      destruct b2 as [| | g2 vs2]; try discriminate.
      destruct (IRI_eq_dec g1 g2) as [<- | Hneq]; [|discriminate].
      destruct (version_set_intersection vs1 vs2) eqn:Ei; [discriminate|].
      injection H as <-. rewrite <- Ei. cbn [wf_binding].
      destruct H1 as [Hnd1 _]. split.
      * apply NoDup_version_set_intersection. exact Hnd1.
      * rewrite Ei. discriminate.
Qed.

Lemma merge_binding_point_l : forall b1 b2 b t,
  point_val b1 = Some t -> merge_binding b1 b2 = Some b -> b = b1.
Proof.
  intros b1 b2 b t Hp H. unfold merge_binding in H. rewrite Hp in H.
  destruct (in_dec Term_eq_dec t (vals b2)); congruence.
Qed.

Lemma merge_binding_point : forall b1 b2 b,
  merge_binding b1 b2 = Some b ->
  (point_val b1 <> None \/ point_val b2 <> None) ->
  point_val b <> None.
Proof.
  intros b1 b2 b H Hp. unfold merge_binding in H.
  destruct (point_val b1) as [t1|] eqn:E1.
  - destruct (in_dec Term_eq_dec t1 (vals b2)); [|discriminate].
    injection H as <-. rewrite E1. discriminate.
  - destruct (point_val b2) as [t2|] eqn:E2.
    + destruct (in_dec Term_eq_dec t2 (vals b1)); [|discriminate].
      injection H as <-. rewrite E2. discriminate.
    + destruct Hp; contradiction.
Qed.

(** ** Flat Compatibility and Merge (Definitions 5.7 and 5.8) *)

(** m1 ∼_F m2: the two mappings agree on every shared variable. *)
Definition compat_flat (f1 f2 : FMapping) : bool :=
  forallb (fun xt =>
    match lookup (fst xt) f2 with
    | None => true
    | Some t' => if Term_eq_dec (snd xt) t' then true else false
    end) f1.

(** ⋎_F(m1, m2): m1's bindings, then the bindings of m2 on fresh variables. *)
Definition merge_flat (f1 f2 : FMapping) : FMapping :=
  f1 ++ filter (fun xt => negb (memb (fst xt) (keys f1))) f2.

Lemma compat_flat_iff : forall f1 f2,
  compat_flat f1 f2 = true <->
  (forall x t1 t2, In (x, t1) f1 -> lookup x f2 = Some t2 -> t1 = t2).
Proof.
  intros f1 f2. unfold compat_flat. rewrite forallb_forall. split.
  - intros H x t1 t2 Hin Hl. specialize (H _ Hin). simpl in H.
    rewrite Hl in H. destruct (Term_eq_dec t1 t2); congruence.
  - intros H [x t1] Hin. simpl.
    destruct (lookup x f2) as [t2|] eqn:E; [|reflexivity].
    destruct (Term_eq_dec t1 t2) as [|Hneq]; [reflexivity|].
    exfalso. apply Hneq. eapply H; eauto.
Qed.

Lemma lookup_merge_flat : forall f1 f2 x,
  lookup x (merge_flat f1 f2) =
  match lookup x f1 with Some t => Some t | None => lookup x f2 end.
Proof.
  intros f1 f2 x. unfold merge_flat. rewrite lookup_app.
  destruct (lookup x f1) as [t|] eqn:E; [reflexivity|].
  apply lookup_filter_keep. intros t'. cbn [fst]. apply negb_true_iff.
  unfold memb. apply inb_false_iff. apply lookup_None_iff. exact E.
Qed.

Lemma merge_flat_keys : forall f1 f2,
  keys (merge_flat f1 f2) =
  keys f1 ++ filter (fun y => negb (memb y (keys f1))) (keys f2).
Proof.
  intros. unfold merge_flat. rewrite keys_app.
  rewrite (keys_filter _ (fun y => negb (memb y (keys f1))))
    by (intros; reflexivity).
  reflexivity.
Qed.

(** ** Condensed Compatibility and Merge (Definitions 5.25 and 5.26) *)

(** m1 ∼_C m2: every shared variable has compatible bindings. *)
Definition compat_cond (m1 m2 : CMapping) : bool :=
  forallb (fun xb =>
    match lookup (fst xb) m2 with
    | None => true
    | Some b2 => match merge_binding (snd xb) b2 with
                 | Some _ => true
                 | None => false
                 end
    end) m1.

Definition merge_entry (m2 : CMapping) (xb : Var * Binding) : Binding :=
  match lookup (fst xb) m2 with
  | None => snd xb
  | Some b2 => match merge_binding (snd xb) b2 with
               | Some b => b
               | None => snd xb
               end
  end.

(** ⋎_C(m1, m2): shared ζ variables get the intersection of their version
    sets; m2's bindings on fresh variables are appended. *)
Definition merge_cond (m1 m2 : CMapping) : CMapping :=
  map (fun xb => (fst xb, merge_entry m2 xb)) m1
  ++ filter (fun xb => negb (memb (fst xb) (keys m1))) m2.

Lemma compat_cond_iff : forall m1 m2,
  compat_cond m1 m2 = true <->
  (forall x b1 b2, In (x, b1) m1 -> lookup x m2 = Some b2 ->
                   exists b, merge_binding b1 b2 = Some b).
Proof.
  intros m1 m2. unfold compat_cond. rewrite forallb_forall. split.
  - intros H x b1 b2 Hin Hl. specialize (H _ Hin). simpl in H.
    rewrite Hl in H. destruct (merge_binding b1 b2); [eauto | discriminate].
  - intros H [x b1] Hin. simpl.
    destruct (lookup x m2) as [b2|] eqn:E; [|reflexivity].
    destruct (H x b1 b2 Hin E) as [b Hb]. rewrite Hb. reflexivity.
Qed.

Lemma lookup_merge_cond : forall m1 m2 x,
  lookup x (merge_cond m1 m2) =
  match lookup x m1 with
  | Some b1 => Some (merge_entry m2 (x, b1))
  | None => lookup x m2
  end.
Proof.
  intros m1 m2 x. unfold merge_cond. rewrite lookup_app.
  rewrite lookup_map_fst.
  destruct (lookup x m1) as [b1|] eqn:E; [reflexivity|].
  apply lookup_filter_keep. intros b. cbn [fst]. apply negb_true_iff.
  unfold memb. apply inb_false_iff. apply lookup_None_iff. exact E.
Qed.

Lemma merge_cond_keys : forall m1 m2,
  keys (merge_cond m1 m2) =
  keys m1 ++ filter (fun y => negb (memb y (keys m1))) (keys m2).
Proof.
  intros. unfold merge_cond. rewrite keys_app, keys_map_fst.
  rewrite (keys_filter _ (fun y => negb (memb y (keys m1))))
    by (intros; reflexivity).
  reflexivity.
Qed.

Lemma merge_cond_wf : forall m1 m2,
  wf_cmap m1 -> wf_cmap m2 -> wf_cmap (merge_cond m1 m2).
Proof.
  intros m1 m2 [Hk1 Hb1] [Hk2 Hb2]. split.
  - rewrite merge_cond_keys. apply NoDup_app; [exact Hk1 | |].
    + apply NoDup_filter. exact Hk2.
    + intros x Hx Hx'. apply filter_In in Hx'.
      destruct Hx' as [_ Hneg]. apply negb_true_iff in Hneg.
      unfold memb in Hneg. apply (inb_false_iff Var_eq_dec) in Hneg. contradiction.
  - unfold merge_cond. apply Forall_app. split.
    + apply Forall_forall. intros [x b] Hin. apply in_map_iff in Hin.
      destruct Hin as [[x' b1] [Heq Hin]]. simpl in Heq.
      injection Heq as <- <-. simpl. unfold merge_entry. simpl.
      rewrite Forall_forall in Hb1. specialize (Hb1 _ Hin). simpl in Hb1.
      destruct (lookup x' m2) as [b2|] eqn:E; [|exact Hb1].
      destruct (merge_binding b1 b2) as [b|] eqn:Em; [|exact Hb1].
      assert (Hwb2 : wf_binding b2).
      { rewrite Forall_forall in Hb2. apply (Hb2 (x', b2)).
        apply lookup_Some_In. exact E. }
      exact (merge_binding_wf b1 b2 b Hb1 Hwb2 Em).
    + apply Forall_forall. intros xb Hin. apply filter_In in Hin.
      rewrite Forall_forall in Hb2. apply Hb2. tauto.
Qed.

(** Point-valuedness is preserved by merging. *)
Lemma merge_cond_point_on : forall xs m1 m2,
  point_on xs m1 -> point_on xs m2 -> point_on xs (merge_cond m1 m2).
Proof.
  intros xs m1 m2 H1 H2 x b Hx Hl. rewrite lookup_merge_cond in Hl.
  destruct (lookup x m1) as [b1|] eqn:E1.
  - injection Hl as <-. unfold merge_entry. simpl.
    specialize (H1 x b1 Hx E1).
    destruct (lookup x m2) as [b2|] eqn:E2; [|exact H1].
    destruct (merge_binding b1 b2) as [b|] eqn:Em; [|exact H1].
    eapply merge_binding_point; eauto.
  - apply (H2 x b Hx Hl).
Qed.

(** ** Lemma 6.4: Compatibility Preservation *)

(** Flat compatibility of two expansions implies condensed compatibility
    of the condensed mappings. *)
Lemma compat_flat_expand_cond : forall m1 m2 f1 f2,
  NoDup (keys m1) ->
  In f1 (expand m1) -> In f2 (expand m2) ->
  compat_flat f1 f2 = true -> compat_cond m1 m2 = true.
Proof.
  intros m1 m2 f1 f2 Hnd Hf1 Hf2 Hc.
  apply compat_cond_iff. intros x b1 b2 Hin Hl2.
  rewrite compat_flat_iff in Hc.
  pose proof (in_lookup_NoDup x m1 b1 Hnd Hin) as Hl1.
  assert (Hk1 : In x (keys f1)).
  { rewrite (expand_keys m1 f1 Hf1). eapply lookup_In_keys; eauto. }
  assert (Hk2 : In x (keys f2)).
  { rewrite (expand_keys m2 f2 Hf2). eapply lookup_In_keys; eauto. }
  destruct (In_keys_lookup x f1 Hk1) as [t1 Ht1].
  destruct (In_keys_lookup x f2 Hk2) as [t2 Ht2].
  pose proof (Hc x t1 t2 (lookup_Some_In _ _ _ Ht1) Ht2) as Heq. subst t2.
  destruct (expand_lookup m1 f1 x t1 Hf1 Ht1) as [b1' [Hb1' Hv1]].
  destruct (expand_lookup m2 f2 x t1 Hf2 Ht2) as [b2' [Hb2' Hv2]].
  rewrite Hl1 in Hb1'. injection Hb1' as <-.
  rewrite Hl2 in Hb2'. injection Hb2' as <-.
  eapply merge_binding_common; eauto.
Qed.

(** ** Lemma 6.6: Join Cardinality Preservation (membership form) *)

Lemma vals_merge_entry_incl : forall m2 x b1 t,
  NoDup (vals b1) ->
  In t (vals (merge_entry m2 (x, b1))) -> In t (vals b1).
Proof.
  intros m2 x b1 t Hnd Hin. unfold merge_entry in Hin. simpl in Hin.
  destruct (lookup x m2) as [b2|]; [|exact Hin].
  destruct (merge_binding b1 b2) as [b|] eqn:Em; [|exact Hin].
  rewrite (merge_binding_vals b1 b2 b Hnd Em) in Hin.
  apply filter_In in Hin. tauto.
Qed.

(** Every flat mapping with the keys of [m] and lookups in the represented
    values is an expansion of [m]. *)
Lemma in_expand_by_lookup : forall m f,
  NoDup (keys m) -> keys f = keys m ->
  (forall x t, lookup x f = Some t ->
               exists b, lookup x m = Some b /\ In t (vals b)) ->
  In f (expand m).
Proof.
  intros m f Hnd Hkeys Hlk. apply in_expand.
  revert f Hkeys Hlk.
  induction m as [|[x b] m IH]; intros [|[x' t] f] Hkeys Hlk;
    simpl in *; try discriminate; [constructor|].
  injection Hkeys as -> Hkeys.
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  constructor.
  - split; simpl; [reflexivity|].
    specialize (Hlk x t). simpl in Hlk.
    destruct (Var_eq_dec x x); [|contradiction].
    destruct (Hlk eq_refl) as [b' [Hb' Hv]]. injection Hb' as <-. exact Hv.
  - apply IH; auto. intros y t' Hl.
    assert (Hneq : y <> x).
    { intros ->. apply Hnotin. unfold keys in *. rewrite <- Hkeys.
      eapply lookup_In_keys; eauto. }
    specialize (Hlk y t'). simpl in Hlk.
    destruct (Var_eq_dec y x); [contradiction|].
    destruct (Hlk Hl) as [b' [Hb' Hv]]. eauto.
Qed.

(** (⇐) A merge of compatible expansions is an expansion of the condensed
    merge. *)
Lemma expand_merge_of_compat : forall m1 m2 f1 f2,
  NoDup (keys m1) -> NoDup (keys m2) ->
  Forall (fun xb => NoDup (vals (snd xb))) m1 ->
  In f1 (expand m1) -> In f2 (expand m2) -> compat_flat f1 f2 = true ->
  In (merge_flat f1 f2) (expand (merge_cond m1 m2)).
Proof.
  intros m1 m2 f1 f2 Hnd1 Hnd2 Hvals1 Hf1 Hf2 Hc.
  pose proof (compat_flat_expand_cond m1 m2 f1 f2 Hnd1 Hf1 Hf2 Hc) as Hcc.
  rewrite compat_cond_iff in Hcc. rewrite compat_flat_iff in Hc.
  unfold merge_flat, merge_cond.
  apply expand_app_in.
  - (* the m1 part *)
    apply in_expand_by_lookup.
    + rewrite keys_map_fst. exact Hnd1.
    + rewrite keys_map_fst. apply expand_keys. exact Hf1.
    + intros x t Hl.
      destruct (expand_lookup m1 f1 x t Hf1 Hl) as [b1 [Hb1 Hv1]].
      exists (merge_entry m2 (x, b1)). split.
      * rewrite lookup_map_fst, Hb1. reflexivity.
      * unfold merge_entry. simpl.
        destruct (lookup x m2) as [b2|] eqn:E2; [|exact Hv1].
        destruct (Hcc x b1 b2 (lookup_Some_In _ _ _ Hb1) E2) as [b Hb].
        rewrite Hb.
        assert (Hndb1 : NoDup (vals b1)).
        { rewrite Forall_forall in Hvals1. apply (Hvals1 (x, b1)).
          apply lookup_Some_In. exact Hb1. }
        rewrite (merge_binding_vals b1 b2 b Hndb1 Hb).
        apply filter_In. split; [exact Hv1|]. unfold in_vals.
        apply inb_true_iff.
        assert (Hk2 : In x (keys f2)).
        { rewrite (expand_keys _ _ Hf2). eapply lookup_In_keys; eauto. }
        destruct (In_keys_lookup x f2 Hk2) as [t2 Ht2].
        pose proof (Hc x t t2 (lookup_Some_In _ _ _ Hl) Ht2) as Heq. subst t2.
        destruct (expand_lookup m2 f2 x t Hf2 Ht2) as [b2' [Hb2' Hv2]].
        rewrite E2 in Hb2'. injection Hb2' as <-. exact Hv2.
  - (* the m2 part *)
    rewrite (expand_keys _ _ Hf1).
    apply (expand_filter_keys m2 f2 (fun y => negb (memb y (keys m1))) Hf2).
Qed.

(** The witness b of the thesis: a flat expansion of m2 that agrees with a
    given flat mapping f1 on the shared variables and with f2 elsewhere. *)
Definition join_witness (m2 : CMapping) (f1 f2 : FMapping) : FMapping :=
  map (fun xb =>
    (fst xb,
     match lookup (fst xb) f1 with
     | Some t => t
     | None => match lookup (fst xb) f2 with
               | Some t => t
               | None => default_term
               end
     end)) m2.

Lemma join_witness_keys : forall m2 f1 f2, keys (join_witness m2 f1 f2) = keys m2.
Proof. intros. unfold join_witness. apply keys_map_fst. Qed.

Lemma lookup_join_witness : forall m2 f1 f2 x b,
  lookup x m2 = Some b ->
  lookup x (join_witness m2 f1 f2) =
  Some (match lookup x f1 with
        | Some t => t
        | None => match lookup x f2 with Some t => t | None => default_term end
        end).
Proof.
  intros m2 f1 f2 x b H. unfold join_witness. rewrite lookup_map_fst, H.
  reflexivity.
Qed.

(** (⇒) Every expansion of the condensed merge is the merge of two
    compatible expansions. *)
Lemma expand_merge_inv : forall m1 m2 f,
  NoDup (keys m1) -> NoDup (keys m2) ->
  Forall (fun xb => NoDup (vals (snd xb))) m1 ->
  compat_cond m1 m2 = true ->
  In f (expand (merge_cond m1 m2)) ->
  exists f1 f2, In f1 (expand m1) /\ In f2 (expand m2) /\
                compat_flat f1 f2 = true /\ f = merge_flat f1 f2.
Proof.
  intros m1 m2 f Hnd1 Hnd2 Hvals1 Hcc Hf.
  unfold merge_cond in Hf.
  apply expand_app_inv in Hf. destruct Hf as [f1 [f2 [-> [Hf1 Hf2]]]].
  rewrite compat_cond_iff in Hcc.
  set (rest2 := filter (fun xb => negb (memb (fst xb) (keys m1))) m2) in *.
  assert (Hkf1 : keys f1 = keys m1).
  { rewrite (expand_keys _ _ Hf1). apply keys_map_fst. }
  assert (Hkf2 : keys f2 = keys rest2) by (apply expand_keys; exact Hf2).
  assert (Hkrest : keys rest2 = filter (fun y => negb (memb y (keys m1))) (keys m2))
    by (unfold rest2; apply (keys_filter _ (fun y => negb (memb y (keys m1))));
        intros; reflexivity).
  (* f1 is an expansion of m1 *)
  assert (Hf1m1 : In f1 (expand m1)).
  { apply in_expand_by_lookup; auto.
    intros x t Hl.
    destruct (expand_lookup _ _ x t Hf1 Hl) as [b' [Hb' Hv]].
    rewrite lookup_map_fst in Hb'.
    destruct (lookup x m1) as [b1|] eqn:E1; [|discriminate].
    injection Hb' as <-. exists b1. split; [reflexivity|].
    eapply vals_merge_entry_incl; [|exact Hv].
    rewrite Forall_forall in Hvals1. apply (Hvals1 (x, b1)).
    apply lookup_Some_In. exact E1. }
  assert (Hkf2' : keys (join_witness m2 f1 f2) = keys m2) by apply join_witness_keys.
  (* (join_witness m2 f1 f2) is an expansion of m2 *)
  assert (Hf2m2 : In (join_witness m2 f1 f2) (expand m2)).
  { apply in_expand_by_lookup; auto.
    intros x t Hl.
    assert (Hx2 : In x (keys m2)).
    { rewrite <- Hkf2'. eapply lookup_In_keys; eauto. }
    destruct (In_keys_lookup x m2 Hx2) as [b2 Hb2].
    exists b2. split; [exact Hb2|].
    rewrite (lookup_join_witness m2 f1 f2 x b2 Hb2) in Hl. injection Hl as <-.
    destruct (lookup x f1) as [t1|] eqn:Ef1.
    - (* shared variable *)
      destruct (expand_lookup _ _ x t1 Hf1 Ef1) as [b' [Hb' Hv]].
      rewrite lookup_map_fst in Hb'.
      destruct (lookup x m1) as [b1|] eqn:E1; [|discriminate].
      injection Hb' as <-. unfold merge_entry in Hv. simpl in Hv.
      rewrite Hb2 in Hv.
      destruct (Hcc x b1 b2 (lookup_Some_In _ _ _ E1) Hb2) as [b Hb].
      rewrite Hb in Hv.
      assert (Hndb1 : NoDup (vals b1)).
      { rewrite Forall_forall in Hvals1. apply (Hvals1 (x, b1)).
        apply lookup_Some_In. exact E1. }
      rewrite (merge_binding_vals b1 b2 b Hndb1 Hb) in Hv.
      apply filter_In in Hv. destruct Hv as [_ Hv]. unfold in_vals in Hv.
      apply (inb_true_iff Term_eq_dec) in Hv. exact Hv.
    - (* variable of m2 only *)
      assert (Hnot1 : ~ In x (keys m1)).
      { rewrite <- Hkf1. apply lookup_None_iff. exact Ef1. }
      assert (Hlrest : lookup x rest2 = Some b2).
      { unfold rest2. rewrite lookup_filter_keep; [exact Hb2|].
        intros b. cbn [fst]. apply negb_true_iff. unfold memb.
        apply inb_false_iff. exact Hnot1. }
      assert (Hxf2 : In x (keys f2)).
      { rewrite Hkf2. eapply lookup_In_keys; eauto. }
      destruct (In_keys_lookup x f2 Hxf2) as [t2 Ht2].
      rewrite Ht2.
      destruct (expand_lookup _ _ x t2 Hf2 Ht2) as [b' [Hb' Hv]].
      rewrite Hlrest in Hb'. injection Hb' as <-. exact Hv. }
  exists f1, (join_witness m2 f1 f2). split; [exact Hf1m1|]. split; [exact Hf2m2|]. split.
  - (* compatibility *)
    apply compat_flat_iff. intros x t1 t2 Hin Hl.
    assert (Hx2 : In x (keys m2)).
    { rewrite <- Hkf2'. eapply lookup_In_keys; eauto. }
    destruct (In_keys_lookup x m2 Hx2) as [b2 Hb2].
    rewrite (lookup_join_witness m2 f1 f2 x b2 Hb2) in Hl. injection Hl as <-.
    assert (Hl1 : lookup x f1 = Some t1).
    { apply in_lookup_NoDup; [rewrite Hkf1; exact Hnd1 | exact Hin]. }
    rewrite Hl1. reflexivity.
  - (* the merge is f1 ++ f2 *)
    unfold merge_flat. f_equal.
    apply fmap_ext_eq.
    + rewrite Hkf2, Hkrest.
      rewrite (keys_filter _ (fun y => negb (memb y (keys f1))))
        by (intros; reflexivity).
      rewrite Hkf2', Hkf1. reflexivity.
    + rewrite Hkf2, Hkrest. apply NoDup_filter. exact Hnd2.
    + intros y.
      destruct (in_dec Var_eq_dec y (keys f1)) as [Hy1 | Hy1].
      * rewrite lookup_filter_drop.
        -- apply lookup_None_iff. rewrite Hkf2, Hkrest.
           rewrite filter_In. rewrite Hkf1 in Hy1. intros [_ Hneg].
           apply negb_true_iff in Hneg. unfold memb in Hneg.
           apply (inb_false_iff Var_eq_dec) in Hneg. contradiction.
        -- intros t. cbn [fst]. apply negb_false_iff. unfold memb.
           apply inb_true_iff. exact Hy1.
      * rewrite lookup_filter_keep.
        -- destruct (in_dec Var_eq_dec y (keys m2)) as [Hy2 | Hy2].
           ++ destruct (In_keys_lookup y m2 Hy2) as [b2 Hb2].
              rewrite (lookup_join_witness m2 f1 f2 y b2 Hb2).
              assert (Ef1 : lookup y f1 = None)
                by (apply lookup_None_iff; exact Hy1).
              rewrite Ef1.
              assert (Hyrest : In y (keys rest2)).
              { rewrite Hkrest. apply filter_In. split; [exact Hy2|].
                apply negb_true_iff. unfold memb. apply inb_false_iff.
                rewrite <- Hkf1. exact Hy1. }
              rewrite <- Hkf2 in Hyrest.
              destruct (In_keys_lookup y f2 Hyrest) as [t2 Ht2].
              rewrite Ht2. reflexivity.
           ++ assert (E1 : lookup y (join_witness m2 f1 f2) = None).
              { apply lookup_None_iff. rewrite Hkf2'. exact Hy2. }
              rewrite E1. apply lookup_None_iff.
              rewrite Hkf2, Hkrest. rewrite filter_In. tauto.
        -- intros t. cbn [fst]. apply negb_true_iff. unfold memb.
           apply inb_false_iff. exact Hy1.
Qed.

(** ** The Flat Join of two Sequences *)

Definition join_flat (L1 L2 : list FMapping) : list FMapping :=
  flat_map (fun f1 =>
    filter_map (fun f2 =>
      if compat_flat f1 f2 then Some (merge_flat f1 f2) else None) L2) L1.

Lemma in_join_flat : forall L1 L2 f,
  In f (join_flat L1 L2) <->
  exists f1 f2, In f1 L1 /\ In f2 L2 /\ compat_flat f1 f2 = true /\
                f = merge_flat f1 f2.
Proof.
  intros L1 L2 f. unfold join_flat. rewrite in_flat_map. split.
  - intros [f1 [H1 Hf]]. apply in_filter_map in Hf.
    destruct Hf as [f2 [H2 Hf]].
    destruct (compat_flat f1 f2) eqn:E; [|discriminate].
    injection Hf as <-. exists f1, f2. auto.
  - intros [f1 [f2 [H1 [H2 [Hc ->]]]]]. exists f1. split; [exact H1|].
    apply in_filter_map. exists f2. rewrite Hc. auto.
Qed.

Lemma merge_flat_inj_l : forall f1 f1' f2 f2',
  keys f1 = keys f1' -> merge_flat f1 f2 = merge_flat f1' f2' -> f1 = f1'.
Proof.
  intros f1 f1' f2 f2' Hk Heq. unfold merge_flat in Heq.
  apply app_eq_length_prefix in Heq; [tauto|].
  apply (f_equal (@length Var)) in Hk. unfold keys in Hk.
  rewrite !length_map in Hk. exact Hk.
Qed.

Lemma merge_flat_inj_r : forall f1 f2 f2',
  keys f2 = keys f2' -> NoDup (keys f2) ->
  compat_flat f1 f2 = true -> compat_flat f1 f2' = true ->
  merge_flat f1 f2 = merge_flat f1 f2' -> f2 = f2'.
Proof.
  intros f1 f2 f2' Hk2 Hnd2 Hc Hc' Heq.
  unfold merge_flat in Heq. apply app_inv_head in Heq.
  rewrite compat_flat_iff in Hc, Hc'.
  apply fmap_ext_eq; auto.
  intros y.
  destruct (in_dec Var_eq_dec y (keys f1)) as [Hy | Hy].
  - destruct (In_keys_lookup y f1 Hy) as [t1 Ht1].
    apply lookup_Some_In in Ht1.
    destruct (lookup y f2) as [t2|] eqn:E2.
    + assert (Hy2' : In y (keys f2')).
      { rewrite <- Hk2. eapply lookup_In_keys; eauto. }
      destruct (In_keys_lookup y f2' Hy2') as [t2' Ht2'].
      rewrite Ht2'. f_equal. transitivity t1; [symmetry|]; eauto.
    + symmetry. apply lookup_None_iff. rewrite <- Hk2.
      apply lookup_None_iff. exact E2.
  - apply (f_equal (lookup y)) in Heq.
    rewrite !lookup_filter_keep in Heq; [exact Heq | |];
      intros t; cbn [fst]; apply negb_true_iff; unfold memb;
      apply inb_false_iff; exact Hy.
Qed.

Lemma NoDup_join_flat : forall L1 L2 k1 k2,
  NoDup L1 -> NoDup L2 ->
  (forall f, In f L1 -> keys f = k1) ->
  (forall f, In f L2 -> keys f = k2) ->
  NoDup k2 ->
  NoDup (join_flat L1 L2).
Proof.
  intros L1 L2 k1 k2 Hnd1 Hnd2 Hk1 Hk2 Hndk2. unfold join_flat.
  apply NoDup_flat_map; [exact Hnd1 | |].
  - intros f1 H1. apply NoDup_filter_map; [exact Hnd2|].
    intros f2 f2' f H2 H2' E E'.
    destruct (compat_flat f1 f2) eqn:C; [|discriminate].
    destruct (compat_flat f1 f2') eqn:C'; [|discriminate].
    injection E as <-. injection E' as E'.
    symmetry. apply (merge_flat_inj_r f1 f2' f2); auto.
    + rewrite (Hk2 _ H2'), (Hk2 _ H2). reflexivity.
    + rewrite (Hk2 _ H2'). exact Hndk2.
  - intros f1 f1' f H1 H1' Hf Hf'.
    apply in_filter_map in Hf. destruct Hf as [f2 [H2 E]].
    apply in_filter_map in Hf'. destruct Hf' as [f2' [H2' E']].
    destruct (compat_flat f1 f2) eqn:C; [|discriminate].
    destruct (compat_flat f1' f2') eqn:C'; [|discriminate].
    injection E as <-. injection E' as E'.
    symmetry. apply (merge_flat_inj_l f1' f1 f2' f2); [|exact E'].
    rewrite (Hk1 _ H1'), (Hk1 _ H1). reflexivity.
Qed.

(** Lemma 6.6 (Join Cardinality Preservation), as a permutation: the
    expansion of a condensed merge is exactly the flat join of the two
    expansions. *)
Lemma expand_merge_perm : forall m1 m2,
  wf_cmap m1 -> wf_cmap m2 -> compat_cond m1 m2 = true ->
  Permutation (expand (merge_cond m1 m2)) (join_flat (expand m1) (expand m2)).
Proof.
  intros m1 m2 Hwf1 Hwf2 Hcc.
  pose proof (proj1 Hwf1) as Hnd1. pose proof (proj1 Hwf2) as Hnd2.
  pose proof (wf_cmap_NoDup_vals _ Hwf1) as Hv1.
  apply NoDup_Permutation.
  - apply wf_cmap_NoDup_expand. apply merge_cond_wf; assumption.
  - apply (NoDup_join_flat _ _ (keys m1) (keys m2)).
    + apply wf_cmap_NoDup_expand. exact Hwf1.
    + apply wf_cmap_NoDup_expand. exact Hwf2.
    + intros f Hf. apply expand_keys. exact Hf.
    + intros f Hf. apply expand_keys. exact Hf.
    + exact Hnd2.
  - intros f. rewrite in_join_flat. split.
    + intros Hf. apply expand_merge_inv; auto.
    + intros [f1 [f2 [H1 [H2 [Hc ->]]]]].
      apply expand_merge_of_compat; auto.
Qed.

Lemma filter_map_none {A B : Type} (f : A -> option B) l :
  (forall a, In a l -> f a = None) -> filter_map f l = [].
Proof.
  unfold filter_map. induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). simpl. apply IH. auto.
Qed.

Lemma flat_map_nil_in {A B : Type} (f : A -> list B) l :
  (forall a, In a l -> f a = []) -> flat_map f l = [].
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)). simpl. apply IH. auto.
Qed.

(** Contrapositive of Lemma 6.4: incompatible condensed mappings have no
    compatible expansions. *)
Lemma join_flat_expand_incompat : forall m1 m2,
  NoDup (keys m1) -> compat_cond m1 m2 = false ->
  join_flat (expand m1) (expand m2) = [].
Proof.
  intros m1 m2 Hnd Hcc. unfold join_flat.
  apply flat_map_nil_in. intros f1 H1.
  apply filter_map_none. intros f2 H2.
  destruct (compat_flat f1 f2) eqn:C; [|reflexivity].
  pose proof (compat_flat_expand_cond m1 m2 f1 f2 Hnd H1 H2 C). congruence.
Qed.

(** ** Restriction of Mappings (Projection, Definition 5.16) *)

Definition restrict {A : Type} (vars : list Var) (m : list (Var * A))
  : list (Var * A) :=
  filter (fun xa => memb (fst xa) vars) m.

Lemma restrict_keys {A : Type} (vars : list Var) (m : list (Var * A)) :
  keys (restrict vars m) = filter (fun y => memb y vars) (keys m).
Proof.
  unfold restrict. apply (keys_filter _ (fun y => memb y vars)).
  intros; reflexivity.
Qed.

Lemma restrict_wf : forall vars m, wf_cmap m -> wf_cmap (restrict vars m).
Proof.
  intros vars m [Hk Hb]. split.
  - apply NoDup_keys_filter. exact Hk.
  - apply Forall_forall. intros xb Hin. unfold restrict in Hin.
    apply filter_In in Hin. rewrite Forall_forall in Hb. apply Hb. tauto.
Qed.

(** Expansion commutes with restriction, provided that every variable that
    is projected away is point-valued (otherwise multiplicities differ, see
    the discussion of the projection case in Equivalence.v). *)
Lemma expand_restrict : forall vars m,
  (forall x b, In (x, b) m -> memb x vars = false -> point_val b <> None) ->
  expand (restrict vars m) = map (restrict vars) (expand m).
Proof.
  intros vars m. unfold restrict.
  induction m as [|[x b] m IH]; intros Hp; [reflexivity|].
  cbn [expand filter fst].
  destruct (memb x vars) eqn:Em.
  - cbn [expand]. rewrite map_flat_map.
    apply flat_map_ext. intros t.
    rewrite IH by (intros y b' Hin; apply Hp; right; exact Hin).
    rewrite !map_map.
    apply map_ext. intros f. cbn [filter fst]. rewrite Em. reflexivity.
  - assert (Hpt : point_val b <> None)
      by (apply (Hp x b); [left; reflexivity | exact Em]).
    destruct (point_val b) as [t|] eqn:Ept; [|contradiction].
    rewrite (point_val_vals b t Ept). cbn [flat_map]. rewrite app_nil_r.
    rewrite map_map.
    rewrite IH by (intros y b' Hin; apply Hp; right; exact Hin).
    apply map_ext. intros f. cbn [filter fst]. rewrite Em. reflexivity.
Qed.

Lemma restrict_point_on : forall vars xs m,
  point_on xs m -> point_on xs (restrict vars m).
Proof.
  intros vars xs m H x b Hx Hl.
  destruct (memb x vars) eqn:Em.
  - unfold restrict in Hl. rewrite lookup_filter_keep in Hl;
      [apply (H x b Hx Hl)|].
    intros a. cbn [fst]. exact Em.
  - unfold restrict in Hl. rewrite lookup_filter_drop in Hl; [discriminate|].
    intros a. cbn [fst]. exact Em.
Qed.
