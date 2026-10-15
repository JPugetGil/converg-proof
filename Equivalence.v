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
Require Import ConVerG.Promotion.
Require Import ConVerG.Difference.
Require Import ConVerG.Typing.
Require Import ConVerG.FlatAlgebra.
Require Import ConVerG.CondensedAlgebra.
Require Import ConVerG.FlatEvaluation.
Require Import ConVerG.CondensedEvaluation.
Require Import ConVerG.Translation.
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

(** One entry (q, V) of the condensed model matches exactly as the
    versioned quads (q, v), v ∈ V, of the flat model. *)
Lemma match_cond_expand : forall s p o g q vs,
  filter_map (match_flat s p o g) (map (quad_with_version q) vs)
  = match match_cond s p o g (q, vs) with
    | Some m => expand m
    | None => []
    end.
Proof.
  intros s p o g q vs. unfold filter_map. rewrite flat_map_map_comp.
  unfold match_cond, match_term_c, match_flat.
  cbv beta iota delta [quad_with_version vq_subject vq_predicate vq_object
                       vq_graph vq_version fst snd].
  destruct (match_term s (TermIRI (quad_subject q))) as [fs|] eqn:Es;
    [|cbv beta iota; apply flat_map_nil].
  destruct (match_term p (TermIRI (quad_predicate q))) as [fp|] eqn:Ep;
    [|cbv beta iota; apply flat_map_nil].
  destruct (match_term o (quad_object q)) as [fo|] eqn:Eo;
    [|cbv beta iota; apply flat_map_nil].
  cbv beta iota.
  rewrite !expand_encode_app. cbn [expand vals].
  rewrite flat_map_map_comp. rewrite !map_flat_map.
  apply flat_map_ext. intros v. reflexivity.
Qed.

Lemma qp_perm : forall s p o g dF dC,
  Permutation dF (flatten dC) ->
  Permutation (filter_map (match_flat s p o g) dF)
              (flat_map expand (filter_map (match_cond s p o g) dC)).
Proof.
  intros s p o g dF dC HP.
  etransitivity; [apply Permutation_filter_map; exact HP|].
  unfold flatten. rewrite filter_map_flat_map, flat_map_filter_map.
  apply Permutation_refl'. apply flat_map_ext. intros [q vs]. cbn [fst snd].
  change (map (fun v => quad_with_version q v) vs)
    with (map (quad_with_version q) vs).
  rewrite (match_cond_expand s p o g q vs). reflexivity.
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
  cbv beta iota in Hm. injection Hm as <-.
  rewrite Forall_forall in HwfC. specialize (HwfC _ Hqvs). cbn [snd] in HwfC.
  split.
  - split.
    + rewrite !keys_app, !encode_keys, (match_term_keys _ _ _ Es),
        (match_term_keys _ _ _ Ep), (match_term_keys _ _ _ Eo). exact Hnd.
    + rewrite !Forall_app. repeat split; try apply encode_wf.
      constructor; [exact HwfC | constructor].
  - apply env_ok_pointwise. unfold pat_env. rewrite !map_app, <- !app_assoc.
    apply Forall2_app; [apply (match_term_env _ _ _ Es)|].
    apply Forall2_app; [apply (match_term_env _ _ _ Ep)|].
    apply Forall2_app; [apply (match_term_env _ _ _ Eo)|].
    constructor; [split; reflexivity | constructor].
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

Lemma extend_fresh : forall e x env' M,
  ~ In x (flat_expr_vars e) ->
  (forall z, In z (env_domain env') -> In z (flat_expr_vars e)) ->
  Forall (inv env') M -> forall m, In m M -> ~ In x (keys m).
Proof.
  intros e x env' M Hx Hdom H m Hm Hk. apply Hx. apply Hdom.
  rewrite Forall_forall in H. destruct (H m Hm) as [_ O].
  eapply env_ok_keys_domain; eauto.
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

Lemma projection_point : forall env vars m,
  inv (env_raise env (needs env (dropped_vars env vars) Id)) m ->
  forall y b, In (y, b) m -> memb y vars = false -> point_val b <> None.
Proof.
  intros env vars m [[Wk _] O] y b Hin Hy.
  assert (Hl : lookup y m = Some b) by (apply in_lookup_NoDup; assumption).
  destruct (O y b Hl) as [r [Hr Hle]].
  assert (Hdom : In y (env_domain env)).
  { eapply (proj1 (raise_needs_domain _ _ _ _)). eapply env_lookup_in_domain; eauto. }
  assert (Hdrop : In y (dropped_vars env vars)).
  { unfold dropped_vars. apply filter_In. split; [exact Hdom | rewrite Hy; reflexivity]. }
  pose proof (raise_needs_meets env _ Id y r Hdrop Hr) as HId.
  apply point_val_repr. apply Id_leq_point. eapply leq_repr_trans; eauto.
Qed.

(** ** Theorem 6.2 *)

Theorem translate_correct : forall e dF dC,
  wf_flat_expr e -> wf_condensed_model dC -> Permutation dF (flatten dC) ->
  Permutation (eval_flat e dF)
              (flat_map expand (eval_cond (fst (translate e)) dC)) /\
  Forall (inv (snd (translate e))) (eval_cond (fst (translate e)) dC).
Proof.
  intros e dF dC.
  induction e as [s p o g | e1 IH1 e2 IH2 | c e IH | e1 IH1 e2 IH2
                  | e1 IH1 e2 IH2 c | e1 IH1 e2 IH2 c | x ex e IH | e IH vars];
    intros Hwf HwfC HP.
  - (* quad pattern *)
    rewrite translate_qp. cbn [fst snd eval_flat eval_cond]. split.
    + apply qp_perm. exact HP.
    + apply Forall_forall. intros m Hm. apply (qp_inv s p o g dC m Hwf HwfC Hm).
  - (* join *)
    destruct Hwf as [Hwf1 Hwf2].
    destruct (IH1 Hwf1 HwfC HP) as [P1 I1]. destruct (IH2 Hwf2 HwfC HP) as [P2 I2].
    rewrite translate_join. cbn [fst snd eval_flat eval_cond]. split.
    + apply join_perm; [apply (inv_wf _ _ I1) | apply (inv_wf _ _ I2) | exact P1 | exact P2].
    + apply Forall_forall. intros m Hm. eapply join_inv; eauto.
  - (* filter *)
    destruct (IH Hwf HwfC HP) as [P1 I1].
    rewrite translate_filter. cbn [fst snd eval_flat eval_cond].
    set (reqs := needs (snd (translate e)) (expr_vars c) Value).
    pose proof (promote_seq_inv _ reqs _ I1) as I1'.
    pose proof (promote_seq_perm_inv _ reqs _ _ I1 P1) as P1'.
    split.
    + apply filter_perm; [|exact P1'].
      eapply Forall_impl; [|exact I1']. intros m [_ O].
      eapply env_ok_needs_point_on. exact O.
    + apply filter_inv. exact I1'.
  - (* union *)
    destruct Hwf as [Hwf1 Hwf2].
    destruct (IH1 Hwf1 HwfC HP) as [P1 I1]. destruct (IH2 Hwf2 HwfC HP) as [P2 I2].
    rewrite translate_union. cbn [fst snd eval_flat eval_cond]. split.
    + rewrite flat_map_app. apply Permutation_app; assumption.
    + apply union_inv; assumption.
  - (* difference *)
    destruct Hwf as [Hwf1 Hwf2].
    destruct (IH1 Hwf1 HwfC HP) as [P1 I1]. destruct (IH2 Hwf2 HwfC HP) as [P2 I2].
    rewrite translate_diff. cbn [fst snd eval_flat eval_cond].
    set (reqs1 := needs (snd (translate e1)) (expr_vars c) Value).
    set (reqs2 := needs (snd (translate e2)) (expr_vars c) Value).
    pose proof (promote_seq_inv _ reqs1 _ I1) as I1'.
    pose proof (promote_seq_perm_inv _ reqs1 _ _ I1 P1) as P1'.
    pose proof (promote_seq_inv _ reqs2 _ I2) as I2'.
    pose proof (promote_seq_perm_inv _ reqs2 _ _ I2 P2) as P2'.
    split.
    + apply diff_cond_perm;
        [apply (inv_wf _ _ I1') | apply (inv_wf _ _ I2') | | exact P1' | exact P2'].
      intros m1 m2 Hm1 Hm2. rewrite Forall_forall in I1', I2'.
      destruct (I1' m1 Hm1) as [_ O1]. destruct (I2' m2 Hm2) as [_ O2].
      apply merge_cond_point_on; eapply env_ok_needs_point_on; eassumption.
    + apply diff_inv. exact I1'.
  - (* optional *)
    destruct Hwf as [Hwf1 Hwf2].
    destruct (IH1 Hwf1 HwfC HP) as [P1 I1]. destruct (IH2 Hwf2 HwfC HP) as [P2 I2].
    rewrite translate_optional. cbn [fst snd eval_flat eval_cond].
    set (reqs1 := needs (snd (translate e1)) (expr_vars c) Value).
    set (reqs2 := needs (snd (translate e2)) (expr_vars c) Value).
    pose proof (promote_seq_inv _ reqs1 _ I1) as I1'.
    pose proof (promote_seq_perm_inv _ reqs1 _ _ I1 P1) as P1'.
    pose proof (promote_seq_inv _ reqs2 _ I2) as I2'.
    pose proof (promote_seq_perm_inv _ reqs2 _ _ I2 P2) as P2'.
    assert (Q1 : Forall (fun m => point_on (expr_vars c) m) (promote_seq reqs1 (eval_cond (fst (translate e1)) dC))).
    { eapply Forall_impl; [|exact I1']. intros m [_ O]. eapply env_ok_needs_point_on. exact O. }
    assert (Q2 : Forall (fun m => point_on (expr_vars c) m) (promote_seq reqs2 (eval_cond (fst (translate e2)) dC))).
    { eapply Forall_impl; [|exact I2']. intros m [_ O]. eapply env_ok_needs_point_on. exact O. }
    split.
    + apply optional_perm; [apply (inv_wf _ _ I1') | apply (inv_wf _ _ I2') | exact Q1 | exact Q2 | exact P1' | exact P2'].
    + unfold optional_cond. apply Forall_app. split.
      * apply filter_inv. apply Forall_forall. intros m Hm. eapply join_inv; eauto.
      * eapply Forall_impl; [|apply diff_inv; exact I1']. intros m [W O]. split; [exact W|].
        eapply env_ok_weaken; [apply env_meet_weaker_l | exact O].
  - (* extend *)
    destruct Hwf as [Hx Hwf]. destruct (IH Hwf HwfC HP) as [P1 I1].
    rewrite translate_extend. cbn [fst snd eval_flat eval_cond].
    set (reqs := needs (snd (translate e)) (expr_vars ex) Value).
    pose proof (promote_seq_inv _ reqs _ I1) as I1'.
    pose proof (promote_seq_perm_inv _ reqs _ _ I1 P1) as P1'.
    split.
    + apply extend_perm; [|exact P1'].
      eapply Forall_impl; [|exact I1']. intros m [_ O].
      eapply env_ok_needs_point_on. exact O.
    + apply extend_inv; [|exact I1']. intros m Hm.
      eapply (extend_fresh e x); [exact Hx | | exact I1' | exact Hm].
      intros z Hz. apply translate_domain.
      exact (proj1 (raise_needs_domain _ _ _ _) Hz).
  - (* projection *)
    destruct (IH Hwf HwfC HP) as [P1 I1].
    rewrite translate_projection. cbn [fst snd eval_flat eval_cond].
    set (reqs := needs (snd (translate e)) (dropped_vars (snd (translate e)) vars) Id).
    pose proof (promote_seq_inv _ reqs _ I1) as I1'.
    pose proof (promote_seq_perm_inv _ reqs _ _ I1 P1) as P1'.
    split.
    + apply projection_perm; [|exact P1'].
      eapply Forall_impl; [|exact I1']. intros m Hm.
      apply (projection_point _ vars m Hm).
    + apply projection_inv. exact I1'.
Qed.

(** ** Main statements *)

(** Theorem 6.2 (Evaluation Equivalence), with the model correspondence
    of Theorem 6.1 as hypothesis: the flat evaluation of e and the
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
