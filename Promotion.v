(** * Promotion: Representation Transformation Υ

    Thesis, Definition 5.36 (environment transformation Υ) and Lemmas
    6.1 and 6.2 (canonical representation): promoting the representation
    of some variables of a condensed mapping yields a sequence of condensed
    mappings with the same expansion.

    Promotion is defined per variable and per binding: a ζ binding
    (g, V) promoted to ι or ν becomes one point-valued binding per
    version v ∈ V (the versioned IRI VI(v, g)); an ι binding promoted to
    ν is decoded through the dictionary; the marker [•] (ψ) promoted to
    ζ becomes one ζ binding per entry of its catalog (τ_{ψ⇝ζ},
    Definition 5.32), and promoted to ι or ν the composition of the
    elementary translations (end of Definition 5.47).  Promotion never
    lowers a representation.
*)

From Stdlib Require Import List Permutation Bool Lia.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.SolutionMappings.
Import ListNotations.

(** ** Promotion of one binding *)

Definition promote_binding (r : Representation) (b : Binding) : list Binding :=
  match r with
  | Value =>
    match b with
    | BVal t => [BVal t]
    | BId n => [BVal (id_to_val n)]
    | BCond g vs => map (fun v => BVal (TermIRI (vi v g))) vs
    | BAll cat =>
        flat_map (fun gv => map (fun v => BVal (TermIRI (vi v (fst gv)))) (snd gv)) cat
    end
  | Id =>
    match b with
    | BVal t => [BVal t]
    | BId n => [BId n]
    | BCond g vs => map (fun v => BId (val_to_id (TermIRI (vi v g)))) vs
    | BAll cat =>
        flat_map (fun gv => map (fun v => BId (val_to_id (TermIRI (vi v (fst gv)))))
                                (snd gv)) cat
    end
  | Condensed =>
    match b with
    | BAll cat => map (fun gv => BCond (fst gv) (snd gv)) cat
    | _ => [b]
    end
  | UnboundGraph => [b]
  end.

Lemma flat_map_vals_map_BVal : forall (f : Version -> Term) vs,
  flat_map vals (map (fun v => BVal (f v)) vs) = map f vs.
Proof.
  intros f vs. induction vs as [|v vs IH]; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma flat_map_vals_map_BId : forall (f : Version -> Term) vs,
  flat_map vals (map (fun v => BId (val_to_id (f v))) vs) = map f vs.
Proof.
  intros f vs. induction vs as [|v vs IH]; simpl; [reflexivity|].
  rewrite IH, id_to_val_to_id. reflexivity.
Qed.

(** The promoted bindings represent, together, exactly the values of the
    original binding (Lemma 6.1, binding level). *)
Lemma vals_promote_binding : forall r b,
  flat_map vals (promote_binding r b) = vals b.
Proof.
  intros r b. destruct r, b as [t | n | g vs | cat]; simpl; try reflexivity;
    try apply app_nil_r.
  - apply flat_map_vals_map_BVal.
  - rewrite flat_map_flat_map. apply flat_map_ext. intros [g vs].
    apply flat_map_vals_map_BVal.
  - apply flat_map_vals_map_BId.
  - rewrite flat_map_flat_map. apply flat_map_ext. intros [g vs].
    apply flat_map_vals_map_BId.
  - rewrite flat_map_map_comp. reflexivity.
Qed.

Lemma promote_binding_point : forall r b b',
  point_repr r = true -> In b' (promote_binding r b) -> point_val b' <> None.
Proof.
  intros r b b' Hr Hin. destruct r; try discriminate; destruct b; simpl in Hin;
    try (destruct Hin as [<- | []]; simpl; discriminate);
    try (apply in_map_iff in Hin; destruct Hin as [w [<- _]]; simpl; discriminate);
    apply in_flat_map in Hin; destruct Hin as [gv [_ Hin]];
    apply in_map_iff in Hin; destruct Hin as [w [<- _]]; simpl; discriminate.
Qed.

Lemma promote_binding_preserves_point : forall r b b',
  point_val b <> None -> In b' (promote_binding r b) -> point_val b' <> None.
Proof.
  intros r b b' Hb Hin. destruct b; try (exfalso; apply Hb; reflexivity).
  all: destruct r; simpl in Hin; destruct Hin as [<- | []]; simpl; discriminate.
Qed.

Lemma promote_binding_wf : forall r b b',
  wf_binding b -> In b' (promote_binding r b) -> wf_binding b'.
Proof.
  intros r b b' Hwf Hin. destruct r, b; simpl in Hin;
    try (destruct Hin as [<- | []]; simpl; exact I);
    try (apply in_map_iff in Hin; destruct Hin as [w [<- _]]; simpl; exact I);
    try (apply in_flat_map in Hin; destruct Hin as [gv [_ Hin]];
         apply in_map_iff in Hin; destruct Hin as [w [<- _]]; simpl; exact I);
    try (destruct Hin as [<- | []]; exact Hwf).
  (* ψ promoted to ζ: one entry of the catalog *)
  apply in_map_iff in Hin. destruct Hin as [[g vs] [<- Hgv]]. simpl.
  destruct Hwf as [_ [Hvs _]]. rewrite Forall_forall in Hvs.
  apply (Hvs (g, vs) Hgv).
Qed.

(** Promotion never lowers a representation, and reaches the requested
    one. *)
Lemma promote_binding_repr : forall r b b',
  In b' (promote_binding r b) ->
  binding_repr b <=_r binding_repr b' /\ r <=_r binding_repr b'.
Proof.
  intros r b b' Hin. destruct r, b; simpl in Hin;
    try (destruct Hin as [<- | []]; simpl; unfold leq_repr; simpl; split; lia);
    try (apply in_map_iff in Hin; destruct Hin as [w [<- _]]; simpl;
         unfold leq_repr; simpl; split; lia);
    apply in_flat_map in Hin; destruct Hin as [gv [_ Hin]];
    apply in_map_iff in Hin; destruct Hin as [w [<- _]]; simpl;
    unfold leq_repr; simpl; split; lia.
Qed.

(** ** Replacing the binding of a variable *)

Definition set_binding (x : Var) (b : Binding) (m : CMapping) : CMapping :=
  map (fun yb => if Var_eq_dec (fst yb) x then (x, b) else yb) m.

Lemma keys_set_binding : forall x b m, keys (set_binding x b m) = keys m.
Proof.
  intros x b m. unfold keys, set_binding. rewrite map_map. apply map_ext.
  intros [y b']. simpl. destruct (Var_eq_dec y x); [subst; reflexivity | reflexivity].
Qed.

Lemma lookup_set_binding_same : forall x b m,
  lookup x (set_binding x b m) =
  match lookup x m with Some _ => Some b | None => None end.
Proof.
  intros x b m. induction m as [|[y b'] m IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec y x) as [-> | Hneq]; simpl.
  - destruct (Var_eq_dec x x); [reflexivity | contradiction].
  - destruct (Var_eq_dec x y); [subst; contradiction | exact IH].
Qed.

Lemma lookup_set_binding_other : forall x y b m,
  y <> x -> lookup y (set_binding x b m) = lookup y m.
Proof.
  intros x y b m Hneq. induction m as [|[z b'] m IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec z x) as [-> | Hzx]; simpl.
  - destruct (Var_eq_dec y x); [contradiction | exact IH].
  - destruct (Var_eq_dec y z); [reflexivity | exact IH].
Qed.

Lemma set_binding_not_in : forall x b m,
  ~ In x (keys m) -> set_binding x b m = m.
Proof.
  intros x b m Hnot. induction m as [|[y b'] m IH]; simpl; [reflexivity|].
  destruct (Var_eq_dec y x) as [-> | Hneq].
  - exfalso. apply Hnot. left. reflexivity.
  - f_equal. apply IH. intros Hin. apply Hnot. right. exact Hin.
Qed.

(** ** Promotion of one variable *)

(** Υ_x^r(m): the mappings obtained by replacing the binding of [x] by each
    of its promoted bindings ([m] itself when [x] is unbound). *)
Definition promote_var (x : Var) (r : Representation) (m : CMapping)
  : list CMapping :=
  match lookup x m with
  | None => [m]
  | Some b => map (fun b' => set_binding x b' m) (promote_binding r b)
  end.

Lemma promote_var_keys : forall x r m m',
  In m' (promote_var x r m) -> keys m' = keys m.
Proof.
  intros x r m m' Hin. unfold promote_var in Hin.
  destruct (lookup x m) as [b|].
  - apply in_map_iff in Hin. destruct Hin as [b' [<- _]]. apply keys_set_binding.
  - destruct Hin as [<- | []]. reflexivity.
Qed.

Lemma promote_var_lookup : forall x r m m' y b',
  In m' (promote_var x r m) -> lookup y m' = Some b' ->
  exists b, lookup y m = Some b /\
    ((y <> x /\ b' = b) \/ (y = x /\ In b' (promote_binding r b))).
Proof.
  intros x r m m' y b' Hin Hl. unfold promote_var in Hin.
  destruct (lookup x m) as [b|] eqn:Ex.
  - apply in_map_iff in Hin. destruct Hin as [b'' [<- Hb'']].
    destruct (Var_eq_dec y x) as [-> | Hneq].
    + rewrite lookup_set_binding_same, Ex in Hl. injection Hl as <-.
      exists b. split; [exact Ex | right; split; [reflexivity | exact Hb'']].
    + rewrite lookup_set_binding_other in Hl by exact Hneq.
      exists b'. split; [exact Hl | left; split; [exact Hneq | reflexivity]].
  - destruct Hin as [<- | []]. exists b'. split; [exact Hl|].
    left. split; [|reflexivity]. intros ->. congruence.
Qed.

Lemma promote_var_wf : forall x r m m',
  wf_cmap m -> In m' (promote_var x r m) -> wf_cmap m'.
Proof.
  intros x r m m' [Hk Hb] Hin. split.
  - rewrite (promote_var_keys x r m m' Hin). exact Hk.
  - apply Forall_forall. intros [y b'] Hin'.
    assert (Hl : lookup y m' = Some b').
    { apply in_lookup_NoDup;
        [rewrite (promote_var_keys x r m m' Hin); exact Hk | exact Hin']. }
    destruct (promote_var_lookup x r m m' y b' Hin Hl)
      as [b [Hlb [[_ ->] | [_ Hpb]]]].
    + rewrite Forall_forall in Hb. apply (Hb (y, b)).
      apply lookup_Some_In. exact Hlb.
    + eapply promote_binding_wf; [|exact Hpb]. rewrite Forall_forall in Hb.
      apply (Hb (y, b)). apply lookup_Some_In. exact Hlb.
Qed.

(** Lemma 6.1 / 6.2 (one variable): promotion preserves the expansion. *)
Lemma promote_var_perm : forall x r m,
  NoDup (keys m) ->
  Permutation (flat_map expand (promote_var x r m)) (expand m).
Proof.
  intros x r m Hnd. induction m as [|[y b] m IH].
  - simpl. reflexivity.
  - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
    specialize (IH Hnd).
    unfold promote_var. cbn [lookup]. destruct (Var_eq_dec x y) as [-> | Hneq].
    + (* the promoted variable is at the head *)
      rewrite (map_ext_in _ (fun b' => (y, b') :: m)).
      2:{ intros b' _. unfold set_binding. simpl.
          destruct (Var_eq_dec y y); [|contradiction].
          f_equal. apply set_binding_not_in. exact Hnotin. }
      rewrite flat_map_map_comp.
      transitivity (flat_map (fun t => map (fun f => (y, t) :: f) (expand m))
                             (flat_map vals (promote_binding r b))).
      { rewrite flat_map_flat_map. reflexivity. }
      rewrite vals_promote_binding. reflexivity.
    + destruct (lookup x m) as [b0|] eqn:Ex.
      * (* the promoted variable is in the tail *)
        rewrite (map_ext_in _ (fun b' => (y, b) :: set_binding x b' m)).
        2:{ intros b' _. unfold set_binding. simpl.
            destruct (Var_eq_dec y x); [congruence | reflexivity]. }
        rewrite flat_map_map_comp. cbn [expand].
        etransitivity.
        { apply (flat_map_swap
                   (fun b' t => map (fun f => (y, t) :: f)
                                    (expand (set_binding x b' m)))). }
        apply Permutation_flat_map_ext. intros t _.
        transitivity (map (fun f => (y, t) :: f)
                          (flat_map (fun b' => expand (set_binding x b' m))
                                    (promote_binding r b0))).
        { rewrite map_flat_map. reflexivity. }
        apply Permutation_map.
        unfold promote_var in IH. rewrite Ex in IH.
        rewrite flat_map_map_comp in IH. exact IH.
      * simpl. rewrite app_nil_r. reflexivity.
Qed.

(** ** Promotion of a list of requirements *)

(** Υ_reqs(m): promote the variables of [reqs] one after the other. *)
Fixpoint promote (reqs : list (Var * Representation)) (m : CMapping)
  : list CMapping :=
  match reqs with
  | [] => [m]
  | (x, r) :: reqs' => flat_map (promote reqs') (promote_var x r m)
  end.

Lemma promote_keys : forall reqs m m',
  In m' (promote reqs m) -> keys m' = keys m.
Proof.
  induction reqs as [|[x r] reqs IH]; simpl; intros m m' Hin.
  - destruct Hin as [<- | []]. reflexivity.
  - apply in_flat_map in Hin. destruct Hin as [m1 [H1 H2]].
    rewrite (IH m1 m' H2). apply (promote_var_keys x r m m1 H1).
Qed.

Lemma promote_wf : forall reqs m m',
  wf_cmap m -> In m' (promote reqs m) -> wf_cmap m'.
Proof.
  induction reqs as [|[x r] reqs IH]; simpl; intros m m' Hwf Hin.
  - destruct Hin as [<- | []]. exact Hwf.
  - apply in_flat_map in Hin. destruct Hin as [m1 [H1 H2]].
    apply (IH m1 m'); [|exact H2]. eapply promote_var_wf; eauto.
Qed.

(** Lemma 6.2 (Canonical Representation): Υ preserves the expansion. *)
Lemma promote_perm : forall reqs m,
  NoDup (keys m) ->
  Permutation (flat_map expand (promote reqs m)) (expand m).
Proof.
  induction reqs as [|[x r] reqs IH]; simpl; intros m Hnd.
  - rewrite app_nil_r. reflexivity.
  - rewrite flat_map_flat_map.
    transitivity (flat_map expand (promote_var x r m)).
    + apply Permutation_flat_map_ext. intros m1 H1. apply IH.
      rewrite (promote_var_keys x r m m1 H1). exact Hnd.
    + apply promote_var_perm. exact Hnd.
Qed.

(** What promotion does to each binding: it never lowers a representation,
    it meets every requirement on the variable, and it preserves
    point-valuedness. *)
Lemma promote_lookup : forall reqs m m' y b',
  In m' (promote reqs m) -> lookup y m' = Some b' ->
  exists b, lookup y m = Some b /\
            binding_repr b <=_r binding_repr b' /\
            (forall r, In (y, r) reqs -> r <=_r binding_repr b') /\
            (point_val b <> None -> point_val b' <> None).
Proof.
  induction reqs as [|[x r] reqs IH]; simpl; intros m m' y b' Hin Hl.
  - destruct Hin as [<- | []]. exists b'. repeat split;
      [exact Hl | apply leq_repr_refl | intros r [] | intros H; exact H].
  - apply in_flat_map in Hin. destruct Hin as [m1 [H1 H2]].
    destruct (IH m1 m' y b' H2 Hl) as [b1 [Hb1 [Hle1 [Hreqs Hpt1]]]].
    destruct (promote_var_lookup x r m m1 y b1 H1 Hb1)
      as [b [Hb [[Hneq ->] | [-> Hpb]]]].
    + exists b. repeat split; [exact Hb | exact Hle1 | | exact Hpt1].
      intros r' [Heq | Hin'];
        [injection Heq as <- <-; contradiction | apply Hreqs; exact Hin'].
    + destruct (promote_binding_repr r b b1 Hpb) as [Hle Hr].
      exists b. repeat split; [exact Hb | eapply leq_repr_trans; eauto | |].
      * intros r' [Heq | Hin'];
          [injection Heq as <-; eapply leq_repr_trans; eauto
          | apply Hreqs; exact Hin'].
      * intros Hp. apply Hpt1. eapply promote_binding_preserves_point; eauto.
Qed.

(** Variables whose requirement is point-valued are point-valued after
    promotion. *)
Lemma promote_point : forall reqs m m' x r b',
  In (x, r) reqs -> point_repr r = true ->
  In m' (promote reqs m) -> lookup x m' = Some b' -> point_val b' <> None.
Proof.
  intros reqs m m' x r b' Hin Hr Hm' Hl.
  destruct (promote_lookup reqs m m' x b' Hm' Hl) as [b [_ [_ [Hreqs _]]]].
  apply point_val_repr. eapply point_repr_mono; [apply Hreqs; exact Hin | exact Hr].
Qed.

(** ** Promotion of a sequence *)

Definition promote_seq (reqs : list (Var * Representation))
  (M : list CMapping) : list CMapping :=
  flat_map (promote reqs) M.

Lemma promote_seq_perm : forall reqs M,
  Forall (fun m => NoDup (keys m)) M ->
  Permutation (flat_map expand (promote_seq reqs M)) (flat_map expand M).
Proof.
  intros reqs M H. unfold promote_seq. rewrite flat_map_flat_map.
  apply Permutation_flat_map_ext. intros m Hm. apply promote_perm.
  rewrite Forall_forall in H. apply H. exact Hm.
Qed.

Lemma promote_seq_wf : forall reqs M,
  Forall wf_cmap M -> Forall wf_cmap (promote_seq reqs M).
Proof.
  intros reqs M H. apply Forall_forall. intros m' Hm'.
  unfold promote_seq in Hm'. apply in_flat_map in Hm'.
  destruct Hm' as [m [Hm Hm']]. rewrite Forall_forall in H.
  apply (promote_wf reqs m m' (H m Hm) Hm').
Qed.
