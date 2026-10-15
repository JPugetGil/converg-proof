(** * Equivalence: Evaluation Equivalence (Theorem 6.2)

    Main result of the thesis (Chapter 6): for every well-formed flat
    expression e, the flat evaluation of e over d_F and the condensed
    evaluation of τ(e) over d_C represent the same bag of solutions:

      ⟦e⟧_F(d_F)  ≅  Ξ(⟦τ(e)⟧_C(d_C))

    where ≅ is equality of bags, formalized as [Permutation] of lists.
    The proof is by induction on e, with the invariant that every
    condensed mapping produced is well-formed and respects the result
    environment R(e) (Typing.v).
*)

From Stdlib Require Import List Permutation Bool PeanoNat.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Models.
Require Import ConVerG.Representations.
Require Import ConVerG.Environments.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Require Import ConVerG.Aggregation.
Require Import ConVerG.Promotion.
Require Import ConVerG.Difference.
Require Import ConVerG.Typing.
Require Import ConVerG.FlatAlgebra.
Require Import ConVerG.CondensedAlgebra.
Require Import ConVerG.FlatEvaluation.
Require Import ConVerG.CondensedEvaluation.
Require Import ConVerG.Translation.
Require Import ConVerG.TypeSystem.
Import ListNotations.

(** ** List utilities *)

Lemma Permutation_flat_map_l {A B : Type} (f : A -> list B) (l l' : list A) :
  Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
Proof.
  intros H.
  induction H as [| x l l' H IH | x y l | l l' l'' H1 IH1 H2 IH2]; simpl.
  - reflexivity.
  - apply Permutation_app_head. exact IH.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - etransitivity; eauto.
Qed.

Lemma filter_map_flat_map {A B C : Type} (f : B -> option C) (g : A -> list B)
      (l : list A) :
  filter_map f (flat_map g l) = flat_map (fun a => filter_map f (g a)) l.
Proof. unfold filter_map. apply flat_map_flat_map. Qed.

Lemma Permutation_filter_map {A B : Type} (f : A -> option B) (l l' : list A) :
  Permutation l l' -> Permutation (filter_map f l) (filter_map f l').
Proof. intros H. unfold filter_map. apply Permutation_flat_map_l. exact H. Qed.

(** ** The invariant of condensed evaluation *)

Definition inv (env : Environment) (m : CMapping) : Prop :=
  wf_cmap m /\ env_ok env m.

Lemma inv_wf : forall env M, Forall (inv env) M -> Forall wf_cmap M.
Proof. intros env M H. eapply Forall_impl; [|exact H]. intros m [W _]. exact W. Qed.

Lemma promote_seq_inv : forall env reqs M,
  Forall (inv env) M -> Forall (inv (env_raise env reqs)) (promote_seq reqs M).
Proof.
  intros env reqs M H. apply Forall_forall. intros m' Hm'.
  unfold promote_seq in Hm'. apply in_flat_map in Hm'.
  destruct Hm' as [m [Hm Hm']]. rewrite Forall_forall in H.
  destruct (H m Hm) as [Hwf Hok].
  split; [eapply promote_wf; eauto | eapply env_ok_promote; eauto].
Qed.

Lemma promote_seq_perm_inv : forall env reqs M L,
  Forall (inv env) M -> Permutation L (flat_map expand M) ->
  Permutation L (flat_map expand (promote_seq reqs M)).
Proof.
  intros env reqs M L H P. etransitivity; [exact P|]. symmetry.
  apply promote_seq_perm. eapply Forall_impl; [|exact H].
  intros m [[Hk _] _]. exact Hk.
Qed.

Lemma env_ok_cons_fresh : forall env m x r,
  ~ In x (keys m) -> env_ok env m -> env_ok ((x, r) :: env) m.
Proof.
  intros env m x r Hx Hok y b Hl. simpl. destruct (Var_eq_dec y x) as [-> | Hneq].
  - exfalso. apply Hx. eapply lookup_In_keys; eauto.
  - apply (Hok y b Hl).
Qed.

(** ** Quad patterns (QP case) *)

Lemma match_term_shape : forall pt t f,
  match_term pt t = Some f ->
  (exists x, pt = PVar x /\ f = [(x, t)]) \/ (f = [] /\ pat_vars pt = []).
Proof.
  intros [x | t'] t f H; simpl in H.
  - injection H as <-. left. exists x. auto.
  - destruct (Term_eq_dec t t'); [injection H as <-; right; auto | discriminate].
Qed.

Lemma expand_encode_app : forall f m,
  expand (encode f ++ m) = map (fun f' => f ++ f') (expand m).
Proof.
  unfold encode. induction f as [|[x t] f IH]; intros m; simpl.
  - etransitivity; [symmetry; apply (map_id (expand m))|].
    apply map_ext. intros f'. reflexivity.
  - rewrite id_to_val_to_id, app_nil_r, IH, map_map. apply map_ext.
    intros f'. reflexivity.
Qed.

(** A predicate hit by at most one version of a duplicate-free version
    set: the versioned IRI [VI(v, g)] determines [v]. *)
Lemma flat_map_unique_hit : forall {A : Type} (p : Version -> bool) (a : A) vs,
  NoDup vs ->
  (forall v v', In v vs -> In v' vs -> p v = true -> p v' = true -> v = v') ->
  flat_map (fun v => if p v then [a] else []) vs
  = if existsb p vs then [a] else [].
Proof.
  intros A p a vs Hnd Huniq. induction vs as [|v vs IH]; simpl; [reflexivity|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  destruct (p v) eqn:Ev; simpl.
  - f_equal. apply flat_map_nil_in. intros v' Hv'.
    destruct (p v') eqn:Ev'; [|reflexivity].
    exfalso. apply Hnotin.
    rewrite (Huniq v v' (or_introl eq_refl) (or_intror Hv') Ev Ev'). exact Hv'.
  - apply IH; [exact Hnd|]. intros v1 v2 H1 H2. apply Huniq; right; assumption.
Qed.

(** One entry (q, V) of the condensed model matches exactly as the
    versioned quads (q, v), v ∈ V, of the flat model.  When the graph
    position is a constant, at most one version of V can produce the
    versioned IRI, which is why V must be duplicate-free. *)
Lemma match_cond_expand : forall s p o g q vs,
  NoDup vs ->
  filter_map (match_flat s p o g) (map (quad_with_version q) vs)
  = match match_cond s p o g (q, vs) with
    | Some m => expand m
    | None => []
    end.
Proof.
  intros s p o g q vs Hnd. unfold filter_map. rewrite flat_map_map_comp.
  unfold match_cond, match_term_c, match_flat.
  cbv beta iota delta [quad_with_version vq_subject vq_predicate vq_object
                       vq_graph vq_version fst snd].
  destruct (match_term s (TermIRI (quad_subject q))) as [fs|] eqn:Es;
    [|cbv beta iota; apply flat_map_nil].
  destruct (match_term p (TermIRI (quad_predicate q))) as [fp|] eqn:Ep;
    [|cbv beta iota; apply flat_map_nil].
  destruct (match_term o (quad_object q)) as [fo|] eqn:Eo;
    [|cbv beta iota; apply flat_map_nil].
  cbv beta iota. destruct g as [x | t].
  - (* graph variable: bound to (g, V) *)
    cbn [match_graph_c match_term].
    rewrite !expand_encode_app. cbn [expand vals].
    rewrite flat_map_map_comp. rewrite !map_flat_map.
    apply flat_map_ext. intros v. reflexivity.
  - (* graph constant: selects at most one version *)
    cbn [match_graph_c match_term].
    rewrite (flat_map_ext_in _
      (fun v => if (if Term_eq_dec (TermIRI (vi v (quad_graph q))) t then true else false)
                then [fs ++ fp ++ fo ++ []] else []))
      by (intros v _; destruct (Term_eq_dec (TermIRI (vi v (quad_graph q))) t); reflexivity).
    rewrite flat_map_unique_hit; [|exact Hnd|].
    + destruct (existsb _ vs); [|reflexivity].
      rewrite !expand_encode_app. reflexivity.
    + intros v v' _ _ Hv Hv'.
      destruct (Term_eq_dec (TermIRI (vi v (quad_graph q))) t) as [E|]; [|discriminate].
      destruct (Term_eq_dec (TermIRI (vi v' (quad_graph q))) t) as [E'|]; [|discriminate].
      rewrite <- E' in E. injection E as E. apply vi_injective in E. tauto.
Qed.

Lemma qp_perm : forall s p o g dF dC,
  wf_condensed_model dC ->
  Permutation dF (flatten dC) ->
  Permutation (filter_map (match_flat s p o g) dF)
              (flat_map expand (filter_map (match_cond s p o g) dC)).
Proof.
  intros s p o g dF dC [_ HwfC] HP.
  etransitivity; [apply Permutation_filter_map; exact HP|].
  unfold flatten. rewrite filter_map_flat_map, flat_map_filter_map.
  apply Permutation_refl'. apply flat_map_ext_in. intros [q vs] Hqvs. cbn [fst snd].
  change (map (fun v => quad_with_version q v) vs)
    with (map (quad_with_version q) vs).
  rewrite Forall_forall in HwfC. specialize (HwfC _ Hqvs). cbn [snd] in HwfC.
  rewrite (match_cond_expand s p o g q vs (proj1 HwfC)). reflexivity.
Qed.

Lemma encode_keys : forall f, keys (encode f) = keys f.
Proof. intros f. unfold encode, keys. rewrite map_map. reflexivity. Qed.

Lemma match_term_keys : forall pt t f,
  match_term pt t = Some f -> keys f = pat_vars pt.
Proof.
  intros pt t f H.
  destruct (match_term_shape pt t f H) as [[x [-> ->]] | [-> Hp]];
    [reflexivity | rewrite Hp; reflexivity].
Qed.

Lemma match_term_env : forall pt t f,
  match_term pt t = Some f ->
  Forall2 (fun xb xr => fst xb = fst xr /\ binding_repr (snd xb) = snd xr)
          (encode f) (map (fun x => (x, Id)) (pat_vars pt)).
Proof.
  intros pt t f H.
  destruct (match_term_shape pt t f H) as [[x [-> ->]] | [-> Hp]].
  - simpl. constructor; [split; reflexivity | constructor].
  - rewrite Hp. constructor.
Qed.

Lemma encode_wf : forall f, Forall (fun xb => wf_binding (snd xb)) (encode f).
Proof.
  intros f. unfold encode. apply Forall_forall. intros xb Hxb.
  apply in_map_iff in Hxb. destruct Hxb as [xt [<- _]]. exact I.
Qed.

Lemma match_graph_keys : forall g gi vs mg,
  match_graph_c g gi vs = Some mg -> keys mg = pat_vars g.
Proof.
  intros [x | t] gi vs mg H; simpl in H.
  - injection H as <-. reflexivity.
  - destruct (existsb _ vs); [injection H as <-; reflexivity | discriminate].
Qed.

Lemma match_graph_env : forall g gi vs mg,
  match_graph_c g gi vs = Some mg ->
  Forall2 (fun xb xr => fst xb = fst xr /\ binding_repr (snd xb) = snd xr)
          mg (map (fun x => (x, Condensed)) (pat_vars g)).
Proof.
  intros [x | t] gi vs mg H; simpl in H.
  - injection H as <-. simpl. constructor; [split; reflexivity | constructor].
  - destruct (existsb _ vs); [injection H as <-; constructor | discriminate].
Qed.

Lemma match_graph_wf : forall g gi vs mg,
  NoDup vs -> vs <> [] -> match_graph_c g gi vs = Some mg ->
  Forall (fun xb => wf_binding (snd xb)) mg.
Proof.
  intros [x | t] gi vs mg Hnd Hne H; simpl in H.
  - injection H as <-. constructor; [split; assumption | constructor].
  - destruct (existsb _ vs); [injection H as <-; constructor | discriminate].
Qed.

Lemma qp_inv : forall s p o g dC m,
  NoDup (quad_pat_vars s p o g) -> wf_condensed_model dC ->
  In m (filter_map (match_cond s p o g) dC) -> inv (pat_env s p o g) m.
Proof.
  intros s p o g dC m Hnd [_ HwfC] Hm. apply in_filter_map in Hm.
  destruct Hm as [[q vs] [Hqvs Hm]].
  unfold match_cond, match_term_c in Hm. cbn [fst snd] in Hm.
  destruct (match_term s (TermIRI (quad_subject q))) as [fs|] eqn:Es;
    [|cbv beta iota in Hm; discriminate].
  destruct (match_term p (TermIRI (quad_predicate q))) as [fp|] eqn:Ep;
    [|cbv beta iota in Hm; discriminate].
  destruct (match_term o (quad_object q)) as [fo|] eqn:Eo;
    [|cbv beta iota in Hm; discriminate].
  destruct (match_graph_c g (quad_graph q) vs) as [mg|] eqn:Eg;
    [|cbv beta iota in Hm; discriminate].
  cbv beta iota in Hm. injection Hm as <-.
  rewrite Forall_forall in HwfC. specialize (HwfC _ Hqvs). cbn [snd] in HwfC.
  split.
  - split.
    + rewrite !keys_app, !encode_keys, (match_term_keys _ _ _ Es),
        (match_term_keys _ _ _ Ep), (match_term_keys _ _ _ Eo),
        (match_graph_keys _ _ _ _ Eg). exact Hnd.
    + rewrite !Forall_app. repeat split; try apply encode_wf.
      apply (match_graph_wf g (quad_graph q) vs mg (proj1 HwfC) (proj2 HwfC) Eg).
  - apply env_ok_pointwise. unfold pat_env. rewrite !map_app, <- !app_assoc.
    apply Forall2_app; [apply (match_term_env _ _ _ Es)|].
    apply Forall2_app; [apply (match_term_env _ _ _ Ep)|].
    apply Forall2_app; [apply (match_term_env _ _ _ Eo)|].
    apply (match_graph_env _ _ _ _ Eg).
Qed.

(** ** Join *)

Lemma Permutation_join_flat : forall L1 L1' L2 L2',
  Permutation L1 L1' -> Permutation L2 L2' ->
  Permutation (join_flat L1 L2) (join_flat L1' L2').
Proof.
  intros L1 L1' L2 L2' P1 P2. unfold join_flat.
  transitivity
    (flat_map (fun f1 =>
       filter_map (fun f2 =>
         if compat_flat f1 f2 then Some (merge_flat f1 f2) else None) L2') L1).
  - apply Permutation_flat_map_ext. intros f1 _. unfold filter_map.
    apply Permutation_flat_map_l. exact P2.
  - apply Permutation_flat_map_l. exact P1.
Qed.

(** JOIN case of Theorem 6.2 (from Lemmas 6.4 and 6.6). *)
Lemma join_perm : forall M1 M2 L1 L2,
  Forall wf_cmap M1 -> Forall wf_cmap M2 ->
  Permutation L1 (flat_map expand M1) -> Permutation L2 (flat_map expand M2) ->
  Permutation (join_flat L1 L2) (flat_map expand (join_cond M1 M2)).
Proof.
  intros M1 M2 L1 L2 W1 W2 P1 P2.
  etransitivity; [apply Permutation_join_flat; eassumption|].
  unfold join_flat, join_cond. rewrite flat_map_flat_map. rewrite flat_map_flat_map.
  apply Permutation_flat_map_ext. intros m1 Hm1.
  rewrite flat_map_filter_map.
  transitivity
    (flat_map (fun f1 =>
       flat_map (fun m2 =>
         filter_map (fun f2 =>
           if compat_flat f1 f2 then Some (merge_flat f1 f2) else None)
           (expand m2)) M2) (expand m1)).
  { apply Permutation_refl'. apply flat_map_ext. intros f1.
    apply filter_map_flat_map. }
  etransitivity; [apply flat_map_swap|].
  apply Permutation_flat_map_ext. intros m2 Hm2.
  rewrite Forall_forall in W1, W2.
  destruct (compat_cond m1 m2) eqn:E.
  - symmetry. apply expand_merge_perm; [apply W1; exact Hm1 | apply W2; exact Hm2 | exact E].
  - transitivity (join_flat (expand m1) (expand m2)); [reflexivity|].
    rewrite (join_flat_expand_incompat m1 m2 (proj1 (W1 m1 Hm1)) E). reflexivity.
Qed.

Lemma join_inv : forall env1 env2 M1 M2 m,
  Forall (inv env1) M1 -> Forall (inv env2) M2 ->
  In m (join_cond M1 M2) -> inv (env_meet env1 env2) m.
Proof.
  intros env1 env2 M1 M2 m H1 H2 Hm. unfold join_cond in Hm.
  apply in_flat_map in Hm. destruct Hm as [m1 [Hm1 Hm]].
  apply in_filter_map in Hm. destruct Hm as [m2 [Hm2 Hm]].
  destruct (compat_cond m1 m2) eqn:E; [|discriminate]. injection Hm as <-.
  rewrite Forall_forall in H1, H2.
  destruct (H1 m1 Hm1) as [W1 O1]. destruct (H2 m2 Hm2) as [W2 O2].
  split; [apply merge_cond_wf; assumption | apply env_ok_merge_cond; assumption].
Qed.

(** ** Filter *)

Lemma filter_expand_eq : forall c M,
  Forall (fun m => point_on (expr_vars c) m) M ->
  filter (fun f => cond_holds (lk_f f) c) (flat_map expand M)
  = flat_map expand (filter_cond c M).
Proof.
  intros c M H. unfold filter_cond. induction M as [|m M IH]; simpl; [reflexivity|].
  inversion H as [| ? ? Hm HM]; subst. specialize (IH HM).
  rewrite filter_app, IH. destruct (cond_holds (lk_c m) c) eqn:E.
  - simpl. f_equal. apply filter_true_In. intros f Hf.
    rewrite (cond_holds_expand c m f Hf Hm). exact E.
  - rewrite filter_false_In; [reflexivity|]. intros f Hf.
    rewrite (cond_holds_expand c m f Hf Hm). exact E.
Qed.

(** FILTER case of Theorem 6.2 (from Lemma 6.3). *)
Lemma filter_perm : forall c M L,
  Forall (fun m => point_on (expr_vars c) m) M ->
  Permutation L (flat_map expand M) ->
  Permutation (filter_flat c L) (flat_map expand (filter_cond c M)).
Proof.
  intros c M L H P. unfold filter_flat.
  etransitivity; [apply Permutation_filter; exact P|].
  rewrite (filter_expand_eq c M H). reflexivity.
Qed.

Lemma filter_inv : forall env c M,
  Forall (inv env) M -> Forall (inv env) (filter_cond c M).
Proof.
  intros env c M H. apply Forall_forall. intros m Hm. unfold filter_cond in Hm.
  apply filter_In in Hm. rewrite Forall_forall in H. apply H. tauto.
Qed.

(** ** Union *)

Lemma union_inv : forall env1 env2 M1 M2,
  Forall (inv env1) M1 -> Forall (inv env2) M2 ->
  Forall (inv (env_meet env1 env2)) (M1 ++ M2).
Proof.
  intros env1 env2 M1 M2 H1 H2. apply Forall_app. split.
  - eapply Forall_impl; [|exact H1]. intros m [W O]. split; [exact W|].
    eapply env_ok_weaken; [apply env_meet_weaker_l | exact O].
  - eapply Forall_impl; [|exact H2]. intros m [W O]. split; [exact W|].
    eapply env_ok_weaken; [apply env_meet_weaker_r | exact O].
Qed.

(** ** Difference and optional *)

Lemma diff_inv : forall env c M1 M2,
  Forall (inv env) M1 -> Forall (inv env) (diff_cond c M1 M2).
Proof.
  intros env c M1 M2 H. apply Forall_forall. intros s Hs.
  destruct (diff_cond_refines c M1 M2 s Hs) as [m1 [Hm1 Href]].
  rewrite Forall_forall in H. destruct (H m1 Hm1) as [W O].
  pose proof Href as [_ [HW _]].
  split; [apply HW; exact W | eapply env_ok_refines; eauto].
Qed.

Lemma join_cond_point_on : forall c M1 M2,
  Forall (fun m => point_on (expr_vars c) m) M1 ->
  Forall (fun m => point_on (expr_vars c) m) M2 ->
  Forall (fun m => point_on (expr_vars c) m) (join_cond M1 M2).
Proof.
  intros c M1 M2 H1 H2. apply Forall_forall. intros m Hm. unfold join_cond in Hm.
  apply in_flat_map in Hm. destruct Hm as [m1 [Hm1 Hm]].
  apply in_filter_map in Hm. destruct Hm as [m2 [Hm2 Hm]].
  destruct (compat_cond m1 m2); [|discriminate]. injection Hm as <-.
  rewrite Forall_forall in H1, H2. apply merge_cond_point_on; auto.
Qed.

(** OPTIONAL case of Theorem 6.2. *)
Lemma optional_perm : forall c M1 M2 L1 L2,
  Forall wf_cmap M1 -> Forall wf_cmap M2 ->
  Forall (fun m => point_on (expr_vars c) m) M1 ->
  Forall (fun m => point_on (expr_vars c) m) M2 ->
  Permutation L1 (flat_map expand M1) -> Permutation L2 (flat_map expand M2) ->
  Permutation (optional_flat c L1 L2) (flat_map expand (optional_cond c M1 M2)).
Proof.
  intros c M1 M2 L1 L2 W1 W2 Q1 Q2 P1 P2.
  unfold optional_flat, optional_cond. rewrite flat_map_app. apply Permutation_app.
  - apply filter_perm; [apply join_cond_point_on; assumption | apply join_perm; assumption].
  - apply diff_cond_perm; try assumption.
    intros m1 m2 Hm1 Hm2. rewrite Forall_forall in Q1, Q2.
    apply merge_cond_point_on; auto.
Qed.

(** ** Extend (BIND) *)

Lemma extend_expand_eq : forall x ex M,
  Forall (fun m => point_on (expr_vars ex) m) M ->
  map (extend_flat x ex) (flat_map expand M)
  = flat_map expand (map (extend_cond x ex) M).
Proof.
  intros x ex M H. rewrite map_flat_map, flat_map_map_comp. apply flat_map_ext_in.
  intros m Hm. rewrite Forall_forall in H. specialize (H m Hm). cbv beta.
  unfold extend_cond. destruct (eval_expr (lk_c m) ex) as [t|] eqn:E.
  - cbn [expand vals flat_map]. rewrite app_nil_r. apply map_ext_in. intros f Hf.
    unfold extend_flat. rewrite (eval_expr_expand ex m f Hf H), E. reflexivity.
  - etransitivity; [|apply map_id]. apply map_ext_in. intros f Hf.
    unfold extend_flat. rewrite (eval_expr_expand ex m f Hf H), E. reflexivity.
Qed.

Lemma extend_perm : forall x ex M L,
  Forall (fun m => point_on (expr_vars ex) m) M ->
  Permutation L (flat_map expand M) ->
  Permutation (map (extend_flat x ex) L)
              (flat_map expand (map (extend_cond x ex) M)).
Proof.
  intros x ex M L H P. etransitivity; [apply Permutation_map; exact P|].
  rewrite (extend_expand_eq x ex M H). reflexivity.
Qed.

Lemma extend_inv : forall env x ex M,
  (forall m, In m M -> ~ In x (keys m)) -> Forall (inv env) M ->
  Forall (inv ((x, Value) :: env)) (map (extend_cond x ex) M).
Proof.
  intros env x ex M Hfresh H. apply Forall_forall. intros m' Hm'.
  apply in_map_iff in Hm'. destruct Hm' as [m [<- Hm]].
  rewrite Forall_forall in H. destruct (H m Hm) as [[Wk Wb] O].
  specialize (Hfresh m Hm). unfold extend_cond.
  destruct (eval_expr (lk_c m) ex) as [t|].
  - split.
    + split; [simpl; constructor; [exact Hfresh | exact Wk]
             | constructor; [exact I | exact Wb]].
    + apply env_ok_cons. exact O.
  - split; [split; assumption|]. apply env_ok_cons_fresh; assumption.
Qed.

(** ** Projection *)

Lemma projection_expand_eq : forall vars M,
  Forall (fun m => forall y b, In (y, b) m -> memb y vars = false ->
                               point_val b <> None) M ->
  map (restrict vars) (flat_map expand M)
  = flat_map expand (map (restrict vars) M).
Proof.
  intros vars M H. rewrite map_flat_map, flat_map_map_comp. apply flat_map_ext_in.
  intros m Hm. rewrite Forall_forall in H. cbv beta. symmetry.
  apply expand_restrict. apply H. exact Hm.
Qed.

(** PROJECTION case of Theorem 6.2.  The hypothesis that every projected
    away variable is point-valued is essential: projecting away a ζ
    variable bound to n versions would collapse n flat solutions into one
    condensed mapping of cardinality 1.  The translation establishes it by
    promoting those variables to ι first. *)
Lemma projection_perm : forall vars M L,
  Forall (fun m => forall y b, In (y, b) m -> memb y vars = false ->
                               point_val b <> None) M ->
  Permutation L (flat_map expand M) ->
  Permutation (map (restrict vars) L) (flat_map expand (map (restrict vars) M)).
Proof.
  intros vars M L H P. etransitivity; [apply Permutation_map; exact P|].
  rewrite (projection_expand_eq vars M H). reflexivity.
Qed.

Lemma projection_inv : forall env vars M,
  Forall (inv env) M ->
  Forall (inv (env_restrict env vars)) (map (restrict vars) M).
Proof.
  intros env vars M H. apply Forall_forall. intros m' Hm'.
  apply in_map_iff in Hm'. destruct Hm' as [m [<- Hm]].
  rewrite Forall_forall in H. destruct (H m Hm) as [W O].
  split; [apply restrict_wf; exact W | apply env_ok_restrict; exact O].
Qed.

(** ** Grouping and aggregation *)

Lemma env_lookup_map_value : forall x l (rest : Environment),
  In x l ->
  env_lookup x (map (fun y => (y, Value)) l ++ rest) = Some Value.
Proof.
  intros x l rest Hx. rewrite env_lookup_eq, lookup_app.
  induction l as [|y l IH]; simpl; [contradiction|].
  destruct (Var_eq_dec x y) as [-> | Hneq]; [reflexivity|].
  apply IH. destruct Hx as [Hx | Hx]; [congruence | exact Hx].
Qed.

Lemma env_lookup_map_value_r : forall x l (aggs : list Aggregate),
  ~ In x l -> In x (map agg_var aggs) ->
  env_lookup x (map (fun y => (y, Value)) l
                ++ map (fun ag => (agg_var ag, Value)) aggs) = Some Value.
Proof.
  intros x l aggs Hnot Hx. rewrite env_lookup_eq, lookup_app.
  assert (E : lookup x (map (fun y => (y, Value)) l) = None).
  { apply lookup_None_iff. unfold keys. rewrite map_map. cbn [fst].
    rewrite map_id. exact Hnot. }
  rewrite E. induction aggs as [|ag aggs IH]; simpl; [contradiction|].
  destruct (Var_eq_dec x (agg_var ag)) as [-> | Hneq]; [reflexivity|].
  apply IH. destruct Hx as [Hx | Hx]; [congruence | exact Hx].
Qed.

Lemma groupagg_inv : forall env ks aggs M,
  Forall (inv env) M -> NoDup ks -> NoDup (map agg_var aggs) ->
  (forall x, In x (map agg_var aggs) -> ~ In x ks) ->
  Forall (inv (groupagg_env env ks aggs)) (groupagg_cond ks aggs M).
Proof.
  intros env ks aggs M H Hks Haggs Hdisj. apply Forall_forall. intros m' Hm'.
  unfold groupagg_cond in Hm'. apply in_map_iff in Hm'.
  destruct Hm' as [[k members] [<- Hg]]. split.
  - apply to_vals_wf. apply NoDup_keys_group_result; assumption.
  - intros y b Hl. rewrite to_vals_lookup in Hl.
    destruct (lookup y (group_result ks aggs values_c (k, members))) as [t|] eqn:El;
      [|discriminate].
    injection Hl as <-. exists Value. split; [|apply leq_repr_refl].
    unfold group_result in El. cbn [fst snd] in El. rewrite lookup_app in El.
    destruct (lookup y (key_mapping ks k)) as [t'|] eqn:Ek.
    + (* a grouping variable, bound in the key *)
      injection El as <-.
      assert (Hy : In y ks)
        by (apply (key_mapping_keys_incl ks k); eapply lookup_In_keys; eauto).
      assert (Hdom : In y (env_domain env)).
      { destruct (in_groups_key _ _ _ _ _ Hg) as [[-> ->] | [m [Hm <-]]].
        - exfalso. unfold key_mapping in Ek. destruct ks; discriminate Ek.
        - apply key_mapping_lookup_c in Ek. unfold lk_c in Ek.
          destruct (lookup y m) as [b|] eqn:Eb; [|discriminate].
          rewrite Forall_forall in H. destruct (H m Hm) as [_ O].
          eapply env_ok_keys_domain; [exact O | eapply lookup_In_keys; eauto]. }
      unfold groupagg_env. apply env_lookup_map_value. apply filter_In.
      split; [exact Hy|]. unfold in_env_domain. apply inb_true_iff. exact Hdom.
    + (* an aggregate variable *)
      assert (Hy : In y (map agg_var aggs))
        by (eapply agg_bindings_keys_incl; eapply lookup_In_keys; eauto).
      unfold groupagg_env. apply env_lookup_map_value_r; [|exact Hy].
      intros Hin. apply filter_In in Hin. apply (Hdisj y Hy). tauto.
Qed.

(** ** Versioned named graphs (GRAPH ?x { }) *)

Lemma expand_single : forall x b,
  expand [(x, b)] = map (fun t => [(x, t)]) (vals b).
Proof.
  intros x b. cbn [expand]. generalize (vals b). intros ts.
  induction ts as [|t ts IH]; simpl; [reflexivity|]. f_equal; auto.
Qed.

Lemma flat_map_expand_graphs_cond : forall x cat,
  flat_map expand (graphs_cond x cat) = map (fun t => [(x, t)]) (vals (BAll cat)).
Proof.
  intros x cat. unfold graphs_cond. destruct cat as [|gv cat]; [reflexivity|].
  cbn [flat_map]. rewrite app_nil_r. apply expand_single.
Qed.

(** GRAPHS case of Theorem 6.2: the versioned named graphs of the flat
    model are the values of the marker • over the catalog of the
    condensed model. *)
Lemma graphs_perm : forall x dF dC,
  Permutation dF (flatten dC) ->
  Permutation (graphs_flat x dF) (flat_map expand (graphs_cond x (graph_catalog dC))).
Proof.
  intros x dF dC HP. rewrite flat_map_expand_graphs_cond. unfold graphs_flat.
  rewrite <- (map_map (fun gv : IRI * Version => TermIRI (vi (snd gv) (fst gv)))
                      (fun t => [(x, t)])).
  apply Permutation_map.
  destruct (graph_catalog_NoDup dC) as [HndC HvsC].
  apply NoDup_Permutation.
  - apply NoDup_map_inj_in; [|apply NoDup_flat_graphs].
    intros [g v] [g' v'] _ _ Heq. cbn [fst snd] in Heq. injection Heq as Heq.
    apply vi_injective in Heq. destruct Heq as [<- <-]. reflexivity.
  - apply NoDup_vals_BAll; assumption.
  - intros t. rewrite in_map_iff, in_vals_BAll. split.
    + intros [[g v] [<- Hin]]. cbn [fst snd].
      apply (flat_graphs_catalog_pairs dF dC g v HP) in Hin.
      apply in_catalog_pairs in Hin. destruct Hin as [vs [Hin Hv]].
      exists g, vs, v. auto.
    + intros [g [vs [v [Hin [Hv ->]]]]]. exists (g, v). split; [reflexivity|].
      apply (flat_graphs_catalog_pairs dF dC g v HP).
      apply in_catalog_pairs. exists vs. auto.
Qed.

Lemma graphs_inv : forall x dC,
  wf_condensed_model dC ->
  Forall (inv [(x, UnboundGraph)]) (graphs_cond x (graph_catalog dC)).
Proof.
  intros x dC HwfC. unfold graphs_cond.
  destruct (graph_catalog dC) as [|gv cat] eqn:E; [constructor|].
  constructor; [|constructor]. split.
  - split.
    + constructor; [intros [] | constructor].
    + constructor; [|constructor]. cbn [snd wf_binding]. rewrite <- E.
      apply wf_catalog_graph_catalog; [exact HwfC | rewrite E; discriminate].
  - intros y b Hl. simpl in Hl. destruct (Var_eq_dec y x) as [-> | Hneq];
      [|discriminate].
    injection Hl as <-. exists UnboundGraph. simpl.
    destruct (Var_eq_dec x x); [|contradiction].
    split; [reflexivity | apply leq_repr_refl].
Qed.

(** ** Theorem 6.2, for every well-typed condensed expression *)

(** Type soundness and evaluation equivalence: a well-typed condensed
    expression computes, up to expansion, the same bag as the flat
    expression it erases to, and its results respect the environment of
    the typing judgement. *)
Theorem typed_correct : forall ec env dF dC,
  typed ec env -> wf_condensed_model dC -> Permutation dF (flatten dC) ->
  Permutation (eval_flat (erase ec) dF) (flat_map expand (eval_cond ec dC)) /\
  Forall (inv env) (eval_cond ec dC).
Proof.
  intros ec env dF dC H HwfC HP.
  induction H as [s p o g Hnd | e1 e2 env1 env2 T1 IH1 T2 IH2
                  | c e env T IH Hpts | e1 e2 env1 env2 T1 IH1 T2 IH2
                  | e1 e2 c env1 env2 T1 IH1 T2 IH2 Hpts1 Hpts2
                  | e1 e2 c env1 env2 T1 IH1 T2 IH2 Hpts1 Hpts2
                  | x ex e env T IH Hfresh Hpts
                  | e vars env T IH Hdrop
                  | ks aggs e env T IH Hks Haggs Hndk Hnda Hdisj
                  | reqs e env T IH
                  | x];
    cbn [erase eval_flat eval_cond].
  - (* quad pattern *)
    split.
    + apply qp_perm; [exact HwfC | exact HP].
    + apply Forall_forall. intros m Hm. apply (qp_inv s p o g dC m Hnd HwfC Hm).
  - (* join *)
    destruct IH1 as [P1 I1]. destruct IH2 as [P2 I2]. split.
    + apply join_perm; [apply (inv_wf _ _ I1) | apply (inv_wf _ _ I2) | exact P1 | exact P2].
    + apply Forall_forall. intros m Hm. eapply join_inv; eauto.
  - (* filter *)
    destruct IH as [P1 I1]. split.
    + apply filter_perm; [|exact P1].
      eapply Forall_impl; [|exact I1]. intros m [_ O].
      eapply env_meets_point_on; [exact O | apply value_greatest | exact Hpts].
    + apply filter_inv. exact I1.
  - (* union *)
    destruct IH1 as [P1 I1]. destruct IH2 as [P2 I2]. split.
    + rewrite flat_map_app. apply Permutation_app; assumption.
    + apply union_inv; assumption.
  - (* difference *)
    destruct IH1 as [P1 I1]. destruct IH2 as [P2 I2]. split.
    + apply diff_cond_perm;
        [apply (inv_wf _ _ I1) | apply (inv_wf _ _ I2) | | exact P1 | exact P2].
      intros m1 m2 Hm1 Hm2. rewrite Forall_forall in I1, I2.
      destruct (I1 m1 Hm1) as [_ O1]. destruct (I2 m2 Hm2) as [_ O2].
      apply merge_cond_point_on;
        eapply env_meets_point_on; try eassumption; apply value_greatest.
    + apply diff_inv. exact I1.
  - (* optional *)
    destruct IH1 as [P1 I1]. destruct IH2 as [P2 I2].
    assert (Q1 : Forall (fun m => point_on (expr_vars c) m) (eval_cond e1 dC)).
    { eapply Forall_impl; [|exact I1]. intros m [_ O].
      eapply env_meets_point_on; [exact O | apply value_greatest | exact Hpts1]. }
    assert (Q2 : Forall (fun m => point_on (expr_vars c) m) (eval_cond e2 dC)).
    { eapply Forall_impl; [|exact I2]. intros m [_ O].
      eapply env_meets_point_on; [exact O | apply value_greatest | exact Hpts2]. }
    split.
    + apply optional_perm;
        [apply (inv_wf _ _ I1) | apply (inv_wf _ _ I2) | exact Q1 | exact Q2
        | exact P1 | exact P2].
    + unfold optional_cond. apply Forall_app. split.
      * apply filter_inv. apply Forall_forall. intros m Hm. eapply join_inv; eauto.
      * eapply Forall_impl; [|apply diff_inv; exact I1]. intros m [W O].
        split; [exact W|]. eapply env_ok_weaken; [apply env_meet_weaker_l | exact O].
  - (* extend *)
    destruct IH as [P1 I1]. split.
    + apply extend_perm; [|exact P1].
      eapply Forall_impl; [|exact I1]. intros m [_ O].
      eapply env_meets_point_on; [exact O | apply leq_repr_refl | exact Hpts].
    + apply extend_inv; [|exact I1]. intros m Hm Hk. apply Hfresh.
      rewrite Forall_forall in I1. destruct (I1 m Hm) as [_ O].
      eapply env_ok_keys_domain; eauto.
  - (* projection *)
    destruct IH as [P1 I1]. split.
    + apply projection_perm; [|exact P1].
      eapply Forall_impl; [|exact I1]. intros m [[Wk _] O] y b Hin Hy.
      assert (Hl : lookup y m = Some b) by (apply in_lookup_NoDup; assumption).
      destruct (O y b Hl) as [r [Hr Hle]].
      apply point_val_repr. apply Id_leq_point.
      eapply leq_repr_trans; [apply (Hdrop y r Hr Hy) | exact Hle].
    + apply projection_inv. exact I1.
  - (* grouping and aggregation *)
    destruct IH as [P1 I1]. split.
    + apply groupagg_perm; [apply (inv_wf _ _ I1) | | | exact P1].
      * eapply Forall_impl; [|exact I1]. intros m [_ O].
        eapply env_meets_ids_point_on; eauto.
      * eapply Forall_impl; [|exact I1]. intros m [_ O].
        apply Forall_forall. intros ag Hag. rewrite Forall_forall in Haggs.
        eapply env_meets_point_on; [exact O | apply value_greatest | apply Haggs; exact Hag].
    + apply groupagg_inv; assumption.
  - (* representation transformation *)
    destruct IH as [P1 I1]. split.
    + apply (promote_seq_perm_inv _ reqs _ _ I1 P1).
    + apply promote_seq_inv. exact I1.
  - (* versioned named graphs *)
    split; [apply graphs_perm; exact HP | apply graphs_inv; exact HwfC].
Qed.

(** The translation τ: its output is well-typed and erases to the source
    expression, hence Theorem 6.2 for τ(e). *)
Theorem translate_correct : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC -> Permutation dF (flatten dC) ->
  Permutation (eval_flat e dF)
              (flat_map expand (eval_cond (fst (translate e)) dC)) /\
  Forall (inv (snd (translate e))) (eval_cond (fst (translate e)) dC).
Proof.
  intros e dF dC Hwf HwfC HP.
  pose proof (typed_correct _ _ dF dC (translate_typed e Hwf) HwfC HP) as H.
  rewrite erase_translate in H. exact H.
Qed.

(** ** Main statements *)

(** Theorem 6.2 (Evaluation Equivalence) for an arbitrary well-typed
    condensed expression, with the model correspondence of Theorem 6.1 as
    hypothesis. *)
Theorem typed_evaluation_equivalence : forall ec env dF dC,
  typed ec env -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Permutation (eval_flat (erase ec) dF) (flat_map expand (eval_cond ec dC)).
Proof.
  intros ec env dF dC T HwfC Hnd Hcorr.
  apply (typed_correct ec env dF dC T HwfC).
  apply models_correspond_Permutation; assumption.
Qed.

(** Type soundness: the results of a well-typed expression are well-formed
    and respect the environment of the judgement. *)
Theorem type_soundness : forall ec env dC,
  typed ec env -> wf_condensed_model dC ->
  Forall (fun m => wf_cmap m /\ env_ok env m) (eval_cond ec dC).
Proof.
  intros ec env dC T HwfC.
  exact (proj2 (typed_correct ec env (flatten dC) dC T HwfC (Permutation_refl _))).
Qed.

(** Theorem 6.2 for the translation τ: the flat evaluation of e and the
    expansion of the condensed evaluation of τ(e) are the same bag. *)
Theorem evaluation_equivalence : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Permutation (eval_flat e dF)
              (flat_map expand (eval_cond (translate_expr e) dC)).
Proof.
  intros e dF dC Hwf HwfC Hnd Hcorr. unfold translate_expr.
  apply translate_correct; [exact Hwf | exact HwfC |].
  apply models_correspond_Permutation; assumption.
Qed.

(** The condensed result is well-formed and respects R(e). *)
Theorem condensed_result_wf : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  Forall (fun m => wf_cmap m /\ env_ok (result_env e) m)
         (eval_cond (translate_expr e) dC).
Proof.
  intros e dF dC Hwf HwfC Hnd Hcorr. unfold translate_expr, result_env.
  exact (proj2 (translate_correct e dF dC Hwf HwfC
                  (models_correspond_Permutation dF dC HwfC Hnd Hcorr))).
Qed.

(** Corollary (count preservation, from Lemma 6.7): the number of flat
    solutions is the sum of the cardinalities of the condensed
    mappings. *)
Corollary count_preservation : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  length (eval_flat e dF) = count_condensed (eval_cond (translate_expr e) dC).
Proof.
  intros e dF dC Hwf HwfC Hnd Hcorr.
  rewrite (Permutation_length (evaluation_equivalence e dF dC Hwf HwfC Hnd Hcorr)).
  apply count_condensed_expand.
Qed.

Definition FMapping_eq_dec : forall f1 f2 : FMapping, {f1 = f2} + {f1 <> f2}.
Proof.
  apply list_eq_dec. intros [x t] [y u].
  destruct (Var_eq_dec x y); destruct (Term_eq_dec t u);
    [left; congruence | right; congruence | right; congruence | right; congruence].
Defined.

(** Corollary (multiplicity preservation): every flat solution occurs the
    same number of times in both results. *)
Corollary multiplicity_preservation : forall e dF dC f,
  wf_flat_expr e -> wf_condensed_model dC ->
  NoDup dF -> models_correspond dF dC ->
  count_occ FMapping_eq_dec (eval_flat e dF) f
  = count_occ FMapping_eq_dec (flat_map expand (eval_cond (translate_expr e) dC)) f.
Proof.
  intros e dF dC f Hwf HwfC Hnd Hcorr.
  apply (proj1 (Permutation_count_occ FMapping_eq_dec _ _)).
  apply evaluation_equivalence; assumption.
Qed.
