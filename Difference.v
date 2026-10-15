(** * Difference: Product-Set Difference and the Condensed DIFF Operator

    Thesis, Definition 5.29 and Lemma 5.1 (product-set difference), and
    the DIFF case of Theorem 6.2.

    A condensed mapping [r] denotes the product of the value sets of its
    bindings.  Removing from this product the sub-product denoted by a
    "blocking" mapping [b] (the narrowing of [r] by a compatible mapping
    of the right-hand side) yields a union of pairwise disjoint
    sub-products: for each variable [x] of [r], the slice where [x] is the
    first variable whose value escapes [b].  Each slice is again a
    condensed mapping, so the result stays condensed.
*)

From Stdlib Require Import List Permutation Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Import ListNotations.

(** ** Restricting a binding to a predicate on terms *)

(** The binding representing { t ∈ vals b | p t }, or [None] when this set
    is empty.  Point-valued bindings stay point-valued; ζ bindings keep
    their named graph; ψ bindings keep their representation, with a
    restricted catalog. *)
Definition binding_filter (p : Term -> bool) (b : Binding) : option Binding :=
  match b with
  | BVal t => if p t then Some (BVal t) else None
  | BId n => if p (id_to_val n) then Some (BId n) else None
  | BCond g vs =>
      match filter (fun v => p (TermIRI (vi v g))) vs with
      | [] => None
      | _ :: _ => Some (BCond g (filter (fun v => p (TermIRI (vi v g))) vs))
      end
  | BAll cat =>
      match cat_restrict p cat with
      | [] => None
      | _ :: _ => Some (BAll (cat_restrict p cat))
      end
  end.

Lemma vals_binding_filter : forall p b b',
  binding_filter p b = Some b' -> vals b' = filter p (vals b).
Proof.
  intros p b b' H. destruct b as [t | n | g vs | cat]; simpl in *.
  - destruct (p t) eqn:E; [|discriminate]. injection H as <-. reflexivity.
  - destruct (p (id_to_val n)) eqn:E; [|discriminate]. injection H as <-.
    reflexivity.
  - destruct (filter (fun v => p (TermIRI (vi v g))) vs) eqn:E; [discriminate|].
    injection H as <-. rewrite <- E. cbn [vals]. rewrite filter_map_swap.
    reflexivity.
  - destruct (cat_restrict p cat) eqn:E; [discriminate|].
    injection H as <-. rewrite <- E. cbn [vals]. apply vals_cat_restrict.
Qed.

Lemma binding_filter_None : forall p b,
  binding_filter p b = None -> filter p (vals b) = [].
Proof.
  intros p b H. destruct b as [t | n | g vs | cat]; simpl in *.
  - destruct (p t) eqn:E; [discriminate|]. reflexivity.
  - destruct (p (id_to_val n)) eqn:E; [discriminate|]. reflexivity.
  - destruct (filter (fun v => p (TermIRI (vi v g))) vs) eqn:E; [|discriminate].
    rewrite filter_map_swap. cbv beta. rewrite E. reflexivity.
  - destruct (cat_restrict p cat) eqn:E; [|discriminate].
    rewrite <- vals_cat_restrict, E. reflexivity.
Qed.

Lemma binding_filter_wf : forall p b b',
  wf_binding b -> binding_filter p b = Some b' -> wf_binding b'.
Proof.
  intros p b b' Hwf H. destruct b as [t | n | g vs | cat]; simpl in *.
  - destruct (p t); [injection H as <-; exact I | discriminate].
  - destruct (p (id_to_val n)); [injection H as <-; exact I | discriminate].
  - destruct (filter (fun v => p (TermIRI (vi v g))) vs) eqn:E; [discriminate|].
    injection H as <-. rewrite <- E. simpl. split.
    + apply NoDup_filter. tauto.
    + rewrite E. discriminate.
  - destruct (cat_restrict p cat) eqn:E; [discriminate|].
    injection H as <-. rewrite <- E. simpl. unfold wf_catalog.
    destruct Hwf as [Hnd [Hvs _]].
    destruct (cat_restrict_wf p cat Hnd Hvs) as [Hnd' Hvs'].
    split; [exact Hnd' | split; [exact Hvs' | rewrite E; discriminate]].
Qed.

Lemma binding_filter_repr : forall p b b',
  binding_filter p b = Some b' -> binding_repr b' = binding_repr b.
Proof.
  intros p b b' H. destruct b as [t | n | g vs | cat]; simpl in *.
  - destruct (p t); [injection H as <-; reflexivity | discriminate].
  - destruct (p (id_to_val n)); [injection H as <-; reflexivity | discriminate].
  - destruct (filter (fun v => p (TermIRI (vi v g))) vs); [discriminate|].
    injection H as <-. reflexivity.
  - destruct (cat_restrict p cat); [discriminate|].
    injection H as <-. reflexivity.
Qed.

(** ** Membership of a flat mapping in the product denoted by a mapping *)

(** [in_box b x t]: the value [t] of [x] is allowed by [b] (a variable
    outside the domain of [b] is unconstrained). *)
Definition in_box (b : CMapping) (x : Var) (t : Term) : bool :=
  match lookup x b with
  | Some bx => in_vals bx t
  | None => true
  end.

(** A flat mapping is blocked by [b] when all its values are allowed. *)
Definition blocked_by (b : CMapping) (f : FMapping) : bool :=
  forallb (fun xt => in_box b (fst xt) (snd xt)) f.

(** ** Slices (Definition 5.29) *)

(** The sub-products of [r] that escape [b], one per variable of [r]. *)
Fixpoint slices (r b : CMapping) : list CMapping :=
  match r with
  | [] => []
  | (x, bx) :: r' =>
      (match binding_filter (fun t => negb (in_box b x t)) bx with
       | Some bx' => [(x, bx') :: r']
       | None => []
       end)
      ++
      (match binding_filter (in_box b x) bx with
       | Some bx'' => map (fun s => (x, bx'') :: s) (slices r' b)
       | None => []
       end)
  end.

(** Lemma 5.1 (Product-Set Difference), bag form: the expansions of the
    slices are exactly the expansions of [r] that are not blocked by
    [b]. *)
Lemma slices_perm : forall r b,
  Permutation (flat_map expand (slices r b))
              (filter (fun f => negb (blocked_by b f)) (expand r)).
Proof.
  induction r as [|[x bx] r IH]; intros b.
  - simpl. reflexivity.
  - cbn [slices expand]. rewrite flat_map_app, filter_flat_map.
    transitivity
      (flat_map (fun t => map (fun f => (x, t) :: f) (expand r))
                (filter (fun t => negb (in_box b x t)) (vals bx))
       ++ flat_map (fun t => map (fun f => (x, t) :: f)
                                 (filter (fun f => negb (blocked_by b f))
                                         (expand r)))
                   (filter (in_box b x) (vals bx))).
    + apply Permutation_app.
      * destruct (binding_filter (fun t => negb (in_box b x t)) bx)
          as [bx'|] eqn:Eo.
        -- cbn [flat_map expand]. rewrite app_nil_r.
           rewrite (vals_binding_filter _ _ _ Eo). reflexivity.
        -- rewrite (binding_filter_None _ _ Eo). reflexivity.
      * destruct (binding_filter (in_box b x) bx) as [bx''|] eqn:Ei.
        -- rewrite flat_map_map_comp. cbn [expand].
           rewrite (vals_binding_filter _ _ _ Ei).
           etransitivity.
           { apply (flat_map_swap
                      (fun s t => map (fun f => (x, t) :: f) (expand s))). }
           apply Permutation_flat_map_ext. intros t _.
           transitivity (map (fun f => (x, t) :: f)
                             (flat_map expand (slices r b))).
           { rewrite map_flat_map. reflexivity. }
           apply Permutation_map. apply IH.
        -- rewrite (binding_filter_None _ _ Ei). reflexivity.
    + etransitivity; [apply Permutation_app_comm|].
      symmetry.
      etransitivity; [| apply (flat_map_partition (in_box b x))].
      apply Permutation_refl'. apply flat_map_ext_in. intros t _. cbv beta.
      rewrite filter_map_swap. destruct (in_box b x t) eqn:E.
      * f_equal. apply filter_ext_In. intros f _. unfold blocked_by.
        cbn [forallb fst snd]. rewrite E. reflexivity.
      * f_equal. apply filter_true_In. intros f _. unfold blocked_by.
        cbn [forallb fst snd]. rewrite E. reflexivity.
Qed.

(** ** Structural properties of slices *)

Lemma slices_keys : forall r b s, In s (slices r b) -> keys s = keys r.
Proof.
  induction r as [|[x bx] r IH]; intros b s Hin; simpl in Hin;
    [contradiction|].
  apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - destruct (binding_filter _ bx);
      [destruct Hin as [<- | []]; reflexivity | contradiction].
  - destruct (binding_filter _ bx); [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [s' [<- Hs']]. simpl. f_equal.
    apply (IH b s' Hs').
Qed.

Lemma slices_lookup : forall r b s y b',
  In s (slices r b) -> lookup y s = Some b' ->
  exists bo, lookup y r = Some bo /\
             (b' = bo \/ exists p, binding_filter p bo = Some b').
Proof.
  induction r as [|[x bx] r IH]; intros b s y b' Hin Hl; simpl in Hin;
    [contradiction|].
  apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
  - destruct (binding_filter (fun t => negb (in_box b x t)) bx) as [bx'|] eqn:E;
      [|contradiction].
    destruct Hin as [<- | []]. simpl in Hl |- *. destruct (Var_eq_dec y x).
    + injection Hl as <-. exists bx. split; [reflexivity | right; eexists; exact E].
    + exists b'. split; [exact Hl | left; reflexivity].
  - destruct (binding_filter (in_box b x) bx) as [bx''|] eqn:E; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [s' [<- Hs']].
    simpl in Hl |- *. destruct (Var_eq_dec y x).
    + injection Hl as <-. exists bx. split; [reflexivity | right; eexists; exact E].
    + apply (IH b s' y b' Hs' Hl).
Qed.

(** A mapping [s] refines [r]: same variables, bindings with the same
    representation and fewer values, well-formedness preserved. *)
Definition refines (s r : CMapping) : Prop :=
  keys s = keys r /\
  (wf_cmap r -> wf_cmap s) /\
  (forall y b', lookup y s = Some b' ->
     exists bo, lookup y r = Some bo /\ binding_repr b' = binding_repr bo).

Lemma refines_refl : forall r, refines r r.
Proof.
  intros r. split; [reflexivity|]. split; [intros H; exact H|].
  intros y b' H. exists b'. auto.
Qed.

Lemma refines_trans : forall s1 s2 s3,
  refines s1 s2 -> refines s2 s3 -> refines s1 s3.
Proof.
  intros s1 s2 s3 [K12 [W12 L12]] [K23 [W23 L23]]. split; [congruence|].
  split; [auto|].
  intros y b' H. destruct (L12 y b' H) as [b2 [H2 E2]].
  destruct (L23 y b2 H2) as [b3 [H3 E3]]. exists b3. split; [exact H3 | congruence].
Qed.

Lemma slices_refines : forall r b s, In s (slices r b) -> refines s r.
Proof.
  intros r b s Hin. split; [apply (slices_keys r b s Hin)|]. split.
  - intros [Hk Hb]. split.
    + rewrite (slices_keys r b s Hin). exact Hk.
    + apply Forall_forall. intros [y b'] Hin'.
      assert (Hl : lookup y s = Some b').
      { apply in_lookup_NoDup;
          [rewrite (slices_keys r b s Hin); exact Hk | exact Hin']. }
      destruct (slices_lookup r b s y b' Hin Hl) as [bo [Hbo [-> | [p Hp]]]].
      * rewrite Forall_forall in Hb. apply (Hb (y, bo)).
        apply lookup_Some_In. exact Hbo.
      * eapply binding_filter_wf; [|exact Hp]. rewrite Forall_forall in Hb.
        apply (Hb (y, bo)). apply lookup_Some_In. exact Hbo.
  - intros y b' Hl.
    destruct (slices_lookup r b s y b' Hin Hl) as [bo [Hbo [-> | [p Hp]]]].
    + exists bo. auto.
    + exists bo. split; [exact Hbo | apply (binding_filter_repr p bo b' Hp)].
Qed.

(** ** Residual: difference with a list of blockers *)

Definition residual_step (b : CMapping) (R : list CMapping) : list CMapping :=
  flat_map (fun r => slices r b) R.

(** [r] minus all the sub-products [bs]. *)
Definition residual (r : CMapping) (bs : list CMapping) : list CMapping :=
  fold_left (fun R b => residual_step b R) bs [r].

Lemma residual_step_perm : forall b R,
  Permutation (flat_map expand (residual_step b R))
              (filter (fun f => negb (blocked_by b f)) (flat_map expand R)).
Proof.
  intros b R. unfold residual_step. rewrite flat_map_flat_map, filter_flat_map.
  apply Permutation_flat_map_ext. intros r _. apply slices_perm.
Qed.

Lemma residual_perm_gen : forall bs R,
  Permutation
    (flat_map expand (fold_left (fun R b => residual_step b R) bs R))
    (filter (fun f => forallb (fun b => negb (blocked_by b f)) bs)
            (flat_map expand R)).
Proof.
  induction bs as [|b bs IH]; intros R; simpl.
  - rewrite filter_true_In; [reflexivity | intros; reflexivity].
  - etransitivity; [apply IH|].
    etransitivity; [apply Permutation_filter, residual_step_perm|].
    rewrite filter_filter. apply Permutation_refl'. apply filter_ext_In.
    intros f _. reflexivity.
Qed.

Lemma residual_perm : forall r bs,
  Permutation (flat_map expand (residual r bs))
              (filter (fun f => forallb (fun b => negb (blocked_by b f)) bs)
                      (expand r)).
Proof.
  intros r bs. unfold residual. etransitivity; [apply residual_perm_gen|].
  simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma residual_gen_refines : forall bs R s,
  In s (fold_left (fun R b => residual_step b R) bs R) ->
  exists r, In r R /\ refines s r.
Proof.
  induction bs as [|b bs IH]; intros R s Hin; simpl in Hin.
  - exists s. split; [exact Hin | apply refines_refl].
  - destruct (IH _ s Hin) as [s' [Hs' Href]].
    unfold residual_step in Hs'. apply in_flat_map in Hs'.
    destruct Hs' as [r [Hr Hsl]].
    exists r. split; [exact Hr|].
    eapply refines_trans; [exact Href | apply (slices_refines _ _ _ Hsl)].
Qed.

Lemma residual_refines : forall r bs s, In s (residual r bs) -> refines s r.
Proof.
  intros r bs s Hin.
  destruct (residual_gen_refines bs [r] s Hin) as [r' [[<- | []] H]]. exact H.
Qed.

(** ** The condensed DIFF operator (Definition 5.30) *)

(** Narrowing of [m1] by [m2]: the shared variables take the merged
    binding, the others keep theirs.  This is the left part of the
    condensed merge. *)
Definition narrow (m1 m2 : CMapping) : CMapping :=
  map (fun xb => (fst xb, merge_entry m2 xb)) m1.

Lemma merge_cond_narrow : forall m1 m2,
  merge_cond m1 m2 =
  narrow m1 m2 ++ filter (fun xb => negb (memb (fst xb) (keys m1))) m2.
Proof. reflexivity. Qed.

(** The sub-products of [m1] removed by [M2]: one per compatible mapping
    of [M2] on which the condition holds. *)
Definition blockers (c : SparqlExpr) (M2 : list CMapping) (m1 : CMapping)
  : list CMapping :=
  filter_map (fun m2 =>
    if compat_cond m1 m2 && cond_holds (lk_c (merge_cond m1 m2)) c
    then Some (narrow m1 m2) else None) M2.

Definition diff_cond (c : SparqlExpr) (M1 M2 : list CMapping)
  : list CMapping :=
  flat_map (fun m1 => residual m1 (blockers c M2 m1)) M1.

(** The flat DIFF operator (Definition 5.12). *)
Definition diff_flat (c : SparqlExpr) (L1 L2 : list FMapping) : list FMapping :=
  filter (fun f1 =>
    forallb (fun f2 =>
      negb (compat_flat f1 f2 && cond_holds (lk_f (merge_flat f1 f2)) c)) L2)
    L1.

(** ** Correctness of the condensed DIFF *)

(** A flat mapping of [m1] is blocked by the narrowing of [m1] by [m2]
    exactly when it has a compatible expansion of [m2] on which the
    condition holds. *)
Lemma blocked_iff : forall c m1 m2 f1,
  wf_cmap m1 -> wf_cmap m2 -> In f1 (expand m1) ->
  point_on (expr_vars c) (merge_cond m1 m2) ->
  ((compat_cond m1 m2 && cond_holds (lk_c (merge_cond m1 m2)) c) = true /\
   blocked_by (narrow m1 m2) f1 = true)
  <-> (exists f2, In f2 (expand m2) /\
       (compat_flat f1 f2 && cond_holds (lk_f (merge_flat f1 f2)) c) = true).
Proof.
  intros c m1 m2 f1 Hwf1 Hwf2 Hf1 Hp.
  pose proof (proj1 Hwf1) as Hnd1. pose proof (proj1 Hwf2) as Hnd2.
  pose proof (wf_cmap_NoDup_vals _ Hwf1) as Hv1.
  split.
  - intros [Hcc Hbl]. apply andb_true_iff in Hcc. destruct Hcc as [Hcc Hcond].
    set (rest2 := filter (fun xb => negb (memb (fst xb) (keys m1))) m2).
    assert (Hf' : In (f1 ++ witness_flat rest2) (expand (merge_cond m1 m2))).
    { rewrite merge_cond_narrow. apply expand_app_in.
      - apply in_expand_by_lookup.
        + unfold narrow. rewrite keys_map_fst. exact Hnd1.
        + unfold narrow. rewrite keys_map_fst. apply expand_keys. exact Hf1.
        + intros x t Hl. unfold blocked_by in Hbl. rewrite forallb_forall in Hbl.
          specialize (Hbl (x, t) (lookup_Some_In _ _ _ Hl)). simpl in Hbl.
          unfold in_box in Hbl.
          destruct (lookup x (narrow m1 m2)) as [bn|] eqn:En.
          * exists bn. split; [reflexivity|]. unfold in_vals in Hbl.
            apply (inb_true_iff Term_eq_dec) in Hbl. exact Hbl.
          * exfalso. apply lookup_None_iff in En. apply En. unfold narrow.
            rewrite keys_map_fst. rewrite <- (expand_keys _ _ Hf1).
            eapply lookup_In_keys; eauto.
      - apply witness_flat_in_expand. apply Forall_forall. intros xb Hxb.
        unfold rest2 in Hxb. apply filter_In in Hxb. destruct Hxb as [Hxb _].
        pose proof (wf_cmap_vals_nonempty _ Hwf2) as H2.
        rewrite Forall_forall in H2. apply H2. exact Hxb. }
    destruct (expand_merge_inv m1 m2 _ Hnd1 Hnd2 Hv1 Hcc Hf')
      as [f1' [f2 [Hf1' [Hf2 [Hc Heq]]]]].
    unfold merge_flat in Heq.
    assert (Hlen : length f1 = length f1').
    { assert (Hk : keys f1 = keys f1')
        by (rewrite (expand_keys _ _ Hf1), (expand_keys _ _ Hf1'); reflexivity).
      apply (f_equal (@length Var)) in Hk. unfold keys in Hk.
      rewrite !length_map in Hk. exact Hk. }
    destruct (app_eq_length_prefix _ _ _ _ Hlen Heq) as [<- _].
    exists f2. split; [exact Hf2|]. apply andb_true_iff. split; [exact Hc|].
    rewrite (cond_holds_expand c (merge_cond m1 m2) (merge_flat f1 f2));
      [exact Hcond | | exact Hp].
    apply expand_merge_of_compat; auto.
  - intros [f2 [Hf2 Hc]]. apply andb_true_iff in Hc. destruct Hc as [Hc Hcond].
    pose proof (compat_flat_expand_cond m1 m2 f1 f2 Hnd1 Hf1 Hf2 Hc) as Hcc.
    assert (Hm : In (merge_flat f1 f2) (expand (merge_cond m1 m2)))
      by (apply expand_merge_of_compat; auto).
    split.
    + apply andb_true_iff. split; [exact Hcc|].
      rewrite <- (cond_holds_expand c (merge_cond m1 m2) (merge_flat f1 f2) Hm Hp).
      exact Hcond.
    + unfold blocked_by. apply forallb_forall. intros [x t] Hin. simpl.
      unfold in_box.
      assert (Hl1 : lookup x f1 = Some t).
      { apply in_lookup_NoDup; [rewrite (expand_keys _ _ Hf1); exact Hnd1 | exact Hin]. }
      assert (Hlm : lookup x (merge_flat f1 f2) = Some t).
      { rewrite lookup_merge_flat, Hl1. reflexivity. }
      destruct (expand_lookup _ _ x t Hm Hlm) as [bm [Hbm Hv]].
      rewrite lookup_merge_cond in Hbm.
      assert (Hx1 : In x (keys m1)).
      { rewrite <- (expand_keys _ _ Hf1). eapply lookup_In_keys; eauto. }
      destruct (In_keys_lookup x m1 Hx1) as [b1 Hb1]. rewrite Hb1 in Hbm.
      injection Hbm as <-.
      unfold narrow. rewrite lookup_map_fst, Hb1. unfold in_vals.
      apply inb_true_iff. exact Hv.
Qed.

(** The blocking test on the condensed side agrees with the flat test on
    the expansions. *)
Lemma diff_pred_eq : forall c M2 m1 f1,
  wf_cmap m1 -> Forall wf_cmap M2 -> In f1 (expand m1) ->
  (forall m2, In m2 M2 -> point_on (expr_vars c) (merge_cond m1 m2)) ->
  forallb (fun b => negb (blocked_by b f1)) (blockers c M2 m1)
  = forallb (fun f2 =>
      negb (compat_flat f1 f2 && cond_holds (lk_f (merge_flat f1 f2)) c))
      (flat_map expand M2).
Proof.
  intros c M2 m1 f1 Hwf1 Hwf2 Hf1 Hp.
  apply eq_true_iff_eq. rewrite !forallb_forall. split.
  - intros H f2 Hf2. apply in_flat_map in Hf2. destruct Hf2 as [m2 [Hm2 Hf2]].
    apply negb_true_iff.
    destruct (compat_flat f1 f2 && cond_holds (lk_f (merge_flat f1 f2)) c)
      eqn:E; [|reflexivity].
    exfalso.
    assert (Hwf2' : wf_cmap m2)
      by (rewrite Forall_forall in Hwf2; apply Hwf2; exact Hm2).
    destruct (proj2 (blocked_iff c m1 m2 f1 Hwf1 Hwf2' Hf1 (Hp m2 Hm2))
                    (ex_intro _ f2 (conj Hf2 E))) as [Hcc Hbl].
    assert (Hin : In (narrow m1 m2) (blockers c M2 m1)).
    { unfold blockers. apply in_filter_map. exists m2. split; [exact Hm2|].
      rewrite Hcc. reflexivity. }
    specialize (H _ Hin). apply negb_true_iff in H. congruence.
  - intros H b Hb. unfold blockers in Hb. apply in_filter_map in Hb.
    destruct Hb as [m2 [Hm2 Hb]].
    destruct (compat_cond m1 m2 && cond_holds (lk_c (merge_cond m1 m2)) c)
      eqn:E; [|discriminate].
    injection Hb as <-.
    apply negb_true_iff. destruct (blocked_by (narrow m1 m2) f1) eqn:Ebl;
      [|reflexivity].
    exfalso.
    assert (Hwf2' : wf_cmap m2)
      by (rewrite Forall_forall in Hwf2; apply Hwf2; exact Hm2).
    destruct (proj1 (blocked_iff c m1 m2 f1 Hwf1 Hwf2' Hf1 (Hp m2 Hm2))
                    (conj E Ebl)) as [f2 [Hf2 Hc]].
    assert (Hf2' : In f2 (flat_map expand M2))
      by (apply in_flat_map; exists m2; auto).
    specialize (H f2 Hf2'). apply negb_true_iff in H. congruence.
Qed.

(** DIFF case of Theorem 6.2. *)
Lemma diff_cond_perm : forall c M1 M2 L1 L2,
  Forall wf_cmap M1 -> Forall wf_cmap M2 ->
  (forall m1 m2, In m1 M1 -> In m2 M2 ->
                 point_on (expr_vars c) (merge_cond m1 m2)) ->
  Permutation L1 (flat_map expand M1) ->
  Permutation L2 (flat_map expand M2) ->
  Permutation (diff_flat c L1 L2) (flat_map expand (diff_cond c M1 M2)).
Proof.
  intros c M1 M2 L1 L2 H1 H2 Hp P1 P2. unfold diff_flat, diff_cond.
  etransitivity; [apply Permutation_filter; exact P1|].
  rewrite filter_flat_map, flat_map_flat_map.
  symmetry. apply Permutation_flat_map_ext. intros m1 Hm1.
  etransitivity; [apply residual_perm|].
  apply Permutation_refl'. apply filter_ext_In. intros f1 Hf1. cbv beta.
  assert (Hwf1 : wf_cmap m1) by (rewrite Forall_forall in H1; apply H1; exact Hm1).
  rewrite (diff_pred_eq c M2 m1 f1 Hwf1 H2 Hf1 (fun m2 Hm2 => Hp m1 m2 Hm1 Hm2)).
  apply forallb_Permutation. symmetry. exact P2.
Qed.

(** Well-formedness and representations are preserved by DIFF. *)
Lemma diff_cond_refines : forall c M1 M2 s,
  In s (diff_cond c M1 M2) -> exists m1, In m1 M1 /\ refines s m1.
Proof.
  intros c M1 M2 s Hin. unfold diff_cond in Hin. apply in_flat_map in Hin.
  destruct Hin as [m1 [Hm1 Hs]]. exists m1. split; [exact Hm1|].
  apply (residual_refines m1 _ s Hs).
Qed.
