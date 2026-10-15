(** * ListUtil: Generic List Lemmas

    Auxiliary results about [filter], [flat_map], [Permutation] and [NoDup]
    that are used throughout the ConVerG formalization.  None of them is
    specific to RDF; they are gathered here to keep the main files focused
    on the thesis material.
*)

From Stdlib Require Import List Permutation Bool.
Import ListNotations.

(** ** Decidable membership *)

Definition inb {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y})
           (x : A) (l : list A) : bool :=
  if in_dec eq_dec x l then true else false.

Lemma inb_true_iff {A : Type} eq_dec (x : A) l :
  inb eq_dec x l = true <-> In x l.
Proof.
  unfold inb. destruct (in_dec eq_dec x l); intuition discriminate.
Qed.

Lemma inb_false_iff {A : Type} eq_dec (x : A) l :
  inb eq_dec x l = false <-> ~ In x l.
Proof.
  unfold inb. destruct (in_dec eq_dec x l); intuition discriminate.
Qed.

(** ** filter_map *)

(** Keep the [Some] results of a partial function. *)
Definition filter_map {A B : Type} (f : A -> option B) (l : list A)
  : list B :=
  flat_map (fun a => match f a with Some b => [b] | None => [] end) l.

Lemma in_filter_map {A B : Type} (f : A -> option B) l b :
  In b (filter_map f l) <-> exists a, In a l /\ f a = Some b.
Proof.
  unfold filter_map. rewrite in_flat_map.
  split.
  - intros [a [Ha Hb]]. destruct (f a) eqn:E; simpl in Hb;
      [destruct Hb as [<- | []] | destruct Hb].
    exists a; auto.
  - intros [a [Ha Hb]]. exists a. rewrite Hb. simpl. auto.
Qed.

Lemma filter_map_app {A B : Type} (f : A -> option B) l1 l2 :
  filter_map f (l1 ++ l2) = filter_map f l1 ++ filter_map f l2.
Proof. unfold filter_map. apply flat_map_app. Qed.

Lemma flat_map_filter_map {A B C : Type} (g : B -> list C)
      (f : A -> option B) l :
  flat_map g (filter_map f l)
  = flat_map (fun a => match f a with Some b => g b | None => [] end) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite flat_map_app, IH. destruct (f a); simpl; [rewrite app_nil_r|];
    reflexivity.
Qed.

(** ** flat_map *)

Lemma flat_map_flat_map {A B C : Type} (g : B -> list C) (f : A -> list B) l :
  flat_map g (flat_map f l) = flat_map (fun a => flat_map g (f a)) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite flat_map_app, IH. reflexivity.
Qed.

Lemma map_flat_map {A B C : Type} (g : B -> C) (f : A -> list B) l :
  map g (flat_map f l) = flat_map (fun a => map g (f a)) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite map_app, IH. reflexivity.
Qed.

Lemma filter_flat_map {A B : Type} (p : B -> bool) (f : A -> list B) l :
  filter p (flat_map f l) = flat_map (fun a => filter p (f a)) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite filter_app, IH. reflexivity.
Qed.

Lemma flat_map_map_comp {A B C : Type} (g : B -> list C) (h : A -> B) l :
  flat_map g (map h l) = flat_map (fun a => g (h a)) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma flat_map_nil {A B : Type} (l : list A) :
  flat_map (fun _ : A => @nil B) l = [].
Proof. induction l; simpl; auto. Qed.

Lemma flat_map_ext_in {A B : Type} (f g : A -> list B) l :
  (forall a, In a l -> f a = g a) -> flat_map f l = flat_map g l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; auto.
Qed.

Lemma length_flat_map_sum {A B : Type} (f : A -> list B) l :
  length (flat_map f l) = fold_right (fun a n => length (f a) + n) 0 l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite length_app, IH. reflexivity.
Qed.

(** ** filter *)

Lemma filter_filter {A : Type} (p q : A -> bool) l :
  filter p (filter q l) = filter (fun x => q x && p x) l.
Proof.
  induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (q a); simpl; [destruct (p a)|]; rewrite IH; reflexivity.
Qed.

Lemma filter_ext_In {A : Type} (p q : A -> bool) l :
  (forall a, In a l -> p a = q a) -> filter p l = filter q l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; auto.
Qed.

Lemma filter_true_In {A : Type} (p : A -> bool) l :
  (forall a, In a l -> p a = true) -> filter p l = l.
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; auto.
Qed.

Lemma filter_false_In {A : Type} (p : A -> bool) l :
  (forall a, In a l -> p a = false) -> filter p l = [].
Proof.
  induction l as [|a l IH]; simpl; intros H; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; auto.
Qed.

(** ** Permutation *)

Lemma Permutation_filter {A : Type} (p : A -> bool) l l' :
  Permutation l l' -> Permutation (filter p l) (filter p l').
Proof.
  intros H.
  induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2]; simpl.
  - constructor.
  - destruct (p x); [constructor|]; exact IH.
  - destruct (p x), (p y); simpl; try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma Permutation_flat_map_ext {A B : Type} (f g : A -> list B) l :
  (forall a, In a l -> Permutation (f a) (g a)) ->
  Permutation (flat_map f l) (flat_map g l).
Proof.
  induction l as [|a l IH]; simpl; intros H; [constructor|].
  apply Permutation_app; auto.
Qed.

Lemma flat_map_app_dist {A B : Type} (f g : A -> list B) l :
  Permutation (flat_map (fun a => f a ++ g a) l)
              (flat_map f l ++ flat_map g l).
Proof.
  induction l as [|a l IH]; simpl; [constructor|].
  rewrite <- !app_assoc.
  apply Permutation_app_head.
  eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
  apply Permutation_app_swap_app.
Qed.

(** Nested [flat_map]s can be swapped, up to permutation. *)
Lemma flat_map_swap {A B C : Type} (h : A -> B -> list C) l1 l2 :
  Permutation (flat_map (fun a => flat_map (fun b => h a b) l2) l1)
              (flat_map (fun b => flat_map (fun a => h a b) l1) l2).
Proof.
  induction l1 as [|a l1 IH]; simpl.
  - rewrite flat_map_nil. constructor.
  - eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
    apply Permutation_sym. apply flat_map_app_dist.
Qed.

(** A [flat_map] whose body depends on a boolean test splits into the two
    parts of the corresponding partition. *)
Lemma flat_map_partition {A B : Type} (p : A -> bool) (f g : A -> list B) l :
  Permutation (flat_map (fun a => if p a then f a else g a) l)
              (flat_map f (filter p l) ++
               flat_map g (filter (fun a => negb (p a)) l)).
Proof.
  induction l as [|a l IH]; simpl; [constructor|].
  destruct (p a); simpl.
  - rewrite <- app_assoc. apply Permutation_app_head. exact IH.
  - eapply Permutation_trans; [apply Permutation_app_head; exact IH|].
    apply Permutation_app_swap_app.
Qed.

Lemma forallb_Permutation {A : Type} (p : A -> bool) l l' :
  Permutation l l' -> forallb p l = forallb p l'.
Proof.
  intros H. apply eq_true_iff_eq.
  rewrite !forallb_forall. split; intros Hall x Hx; apply Hall.
  - eapply Permutation_in; [apply Permutation_sym|]; eauto.
  - eapply Permutation_in; eauto.
Qed.

Lemma existsb_Permutation {A : Type} (p : A -> bool) l l' :
  Permutation l l' -> existsb p l = existsb p l'.
Proof.
  intros H. apply eq_true_iff_eq.
  rewrite !existsb_exists. split; intros [x [Hx Hp]]; exists x; split; auto.
  - eapply Permutation_in; eauto.
  - eapply Permutation_in; [apply Permutation_sym|]; eauto.
Qed.

(** ** NoDup *)

Lemma NoDup_flat_map {A B : Type} (f : A -> list B) l :
  NoDup l ->
  (forall a, In a l -> NoDup (f a)) ->
  (forall a a' x, In a l -> In a' l -> In x (f a) -> In x (f a') -> a = a') ->
  NoDup (flat_map f l).
Proof.
  induction l as [|a l IH]; simpl; intros Hnd Hf Hdisj; [constructor|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  apply NoDup_app.
  - apply Hf. now left.
  - apply IH.
    + exact Hnd.
    + intros a' Ha'. apply Hf. now right.
    + intros a1 a2 x H1 H2 Hx1 Hx2.
      apply (Hdisj a1 a2 x); [now right | now right | exact Hx1 | exact Hx2].
  - intros x Hx Hx'. apply in_flat_map in Hx'.
    destruct Hx' as [a' [Ha' Hxa']].
    assert (a = a') as <-
      by (apply (Hdisj a a' x); [now left | now right | exact Hx | exact Hxa']).
    contradiction.
Qed.

Lemma NoDup_filter_map {A B : Type} (f : A -> option B) l :
  NoDup l ->
  (forall a a' b, In a l -> In a' l -> f a = Some b -> f a' = Some b -> a = a') ->
  NoDup (filter_map f l).
Proof.
  intros Hnd Hinj. unfold filter_map. apply NoDup_flat_map; auto.
  - intros a _. destruct (f a); repeat constructor; auto.
  - intros a a' x Ha Ha' Hx Hx'.
    destruct (f a) eqn:Ea; simpl in Hx; [destruct Hx as [<- | []]|destruct Hx].
    destruct (f a') eqn:Ea'; simpl in Hx'; [destruct Hx' as [Heq | []]|destruct Hx'].
    subst. eapply Hinj; eauto.
Qed.

Lemma NoDup_map_inj_in {A B : Type} (f : A -> B) l :
  (forall a a', In a l -> In a' l -> f a = f a' -> a = a') ->
  NoDup l -> NoDup (map f l).
Proof.
  induction l as [|a l IH]; simpl; intros Hinj Hnd; [constructor|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  constructor.
  - intros Hin. apply in_map_iff in Hin. destruct Hin as [a' [Heq Ha']].
    assert (a = a') by (apply Hinj; auto). subst. contradiction.
  - apply IH; auto.
Qed.

Lemma NoDup_app_disjoint {A : Type} (l1 l2 : list A) x :
  NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  induction l1 as [|a l1 IH]; simpl; intros Hnd Hx; [contradiction|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  destruct Hx as [<- | Hx].
  - intros Hx2. apply Hnotin. apply in_app_iff. auto.
  - apply IH; auto.
Qed.
