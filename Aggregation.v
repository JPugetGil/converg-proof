(** * Aggregation: Grouping and Aggregate Functions

    Thesis, Section 5.3.6 (Definitions 5.37, 5.38 and 5.39) and the
    Group, Aggregation and AggregateJoin cases of Theorem 6.2.

    The three operators of the thesis are fused into one,
    [GroupAgg(ks, aggs, e)] = AggJ(Agg_1, ..., Agg_n) ∘ Gr(ks, e), which is
    the SPARQL 1.1 translation of [SELECT ks (f_i(e_i) AS ?a_i) ... GROUP
    BY ks].  Solutions are grouped by the values of the variables [ks];
    each group yields one solution binding the group key and, for each
    aggregate, its value.

    Aggregate functions are abstract: an aggregate is any function of
    the *bag* of the values of its expression over the group
    ([agg_apply_perm]).  COUNT, SUM, AVG, MIN and MAX are instances.  The
    condensed evaluation is the count-views optimization of
    Definition 5.39: a condensed mapping [m] contributes the value of the
    expression [card(m)] times ([values_c]).  Equivalence then holds for
    every aggregate function at once, because the weighted bag is a
    permutation of the flat bag (Lemma 6.7 with Lemma 6.3).
*)

From Stdlib Require Import List Permutation Bool PeanoNat Lia.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.SolutionMappings.
Require Import ConVerG.Expressions.
Import ListNotations.

(** ** Aggregate functions *)

Parameter AggFun : Type.

(** The value of an aggregate function on the bag of the values of its
    expression over a group; [None] is the SPARQL error (the aggregate
    variable is then unbound).  An element [None] of the bag is the
    error value of the expression on one solution. *)
Parameter agg_apply : AggFun -> list (option Term) -> option Term.

(** Modeling assumption: an aggregate is a function of the bag. *)
Axiom agg_apply_perm : forall a l l',
  Permutation l l' -> agg_apply a l = agg_apply a l'.

(** COUNT, as an example: the number of solutions on which the
    expression is defined. *)
Parameter term_of_nat : nat -> Term.

Definition is_some {A : Type} (o : option A) : bool :=
  match o with Some _ => true | None => false end.

Definition count_values (l : list (option Term)) : option Term :=
  Some (term_of_nat (length (filter is_some l))).

Lemma count_values_perm : forall l l',
  Permutation l l' -> count_values l = count_values l'.
Proof.
  intros l l' H. unfold count_values.
  rewrite (Permutation_length (Permutation_filter is_some l l' H)). reflexivity.
Qed.

(** ** Group keys (Definition 5.37) *)

Definition Key := list (option Term).

Definition OptTerm_eq_dec : forall o1 o2 : option Term, {o1 = o2} + {o1 <> o2}.
Proof.
  intros [t1|] [t2|]; try (right; discriminate); [|left; reflexivity].
  destruct (Term_eq_dec t1 t2); [left; congruence | right; congruence].
Defined.

Definition Key_eq_dec : forall k1 k2 : Key, {k1 = k2} + {k1 <> k2} :=
  list_eq_dec OptTerm_eq_dec.

Definition key_eqb (k1 k2 : Key) : bool :=
  if Key_eq_dec k1 k2 then true else false.

Lemma key_eqb_true : forall k1 k2, key_eqb k1 k2 = true <-> k1 = k2.
Proof.
  intros k1 k2. unfold key_eqb. destruct (Key_eq_dec k1 k2); split; congruence.
Qed.

(** The key of a solution: the values of the grouping variables (an
    unbound variable contributes [None]). *)
Definition key_of (lk : Var -> option Term) (ks : list Var) : Key :=
  map lk ks.

(** ** Grouping *)

(** The groups of a list, by a key function: one group per distinct key,
    with the elements of that key in their original order. *)
Definition group_by {A : Type} (key : A -> Key) (L : list A)
  : list (Key * list A) :=
  map (fun k => (k, filter (fun a => key_eqb (key a) k) L))
      (nodup Key_eq_dec (map key L)).

(** Implicit group: without grouping variable, an empty input still
    yields one empty group (SPARQL 1.1, Section 18.5.1: [Group((1), Ω)]
    for a query with aggregates and no GROUP BY). *)
Definition groups {A : Type} (key : A -> Key) (ks : list Var) (L : list A)
  : list (Key * list A) :=
  match ks, L with
  | [], [] => [([], [])]
  | _, _ => group_by key L
  end.

Lemma groups_nonempty : forall {A : Type} (key : A -> Key) ks (L : list A),
  L <> [] -> groups key ks L = group_by key L.
Proof.
  intros A key [|x ks] [|a L] H; try reflexivity. contradiction.
Qed.

(** A group is either the implicit empty group or has the key of one of
    the elements. *)
Lemma in_groups_key : forall {A : Type} (key : A -> Key) ks (L : list A) k members,
  In (k, members) (groups key ks L) ->
  (k = [] /\ members = []) \/ exists a, In a L /\ key a = k.
Proof.
  intros A key ks L k members Hin.
  destruct L as [|a L].
  - destruct ks as [|x ks]; simpl in Hin.
    + destruct Hin as [Heq | []]. injection Heq as <- <-. left. auto.
    + contradiction.
  - rewrite groups_nonempty in Hin by discriminate. unfold group_by in Hin.
    apply in_map_iff in Hin. destruct Hin as [k' [Heq Hk']].
    injection Heq as <- <-. rewrite nodup_In, in_map_iff in Hk'.
    destruct Hk' as [a' [<- Ha']]. right. exists a'. auto.
Qed.

(** ** The solution of a group (Definition 5.38, AggregateJoin) *)

Definition Aggregate := (Var * AggFun * SparqlExpr)%type.

Definition agg_var (ag : Aggregate) : Var := fst (fst ag).
Definition agg_fun (ag : Aggregate) : AggFun := snd (fst ag).
Definition agg_expr (ag : Aggregate) : SparqlExpr := snd ag.

(** The bindings of the grouping variables, from the key. *)
Definition key_mapping (ks : list Var) (k : Key) : FMapping :=
  filter_map (fun xo : Var * option Term =>
                match snd xo with Some t => Some (fst xo, t) | None => None end)
             (combine ks k).

(** The bindings of the aggregate variables, from the bag of values of
    each expression over the group. *)
Definition agg_bindings (values : SparqlExpr -> list (option Term))
  (aggs : list Aggregate) : FMapping :=
  filter_map (fun ag =>
                match agg_apply (agg_fun ag) (values (agg_expr ag)) with
                | Some t => Some (agg_var ag, t)
                | None => None
                end) aggs.

Definition group_result {A : Type} (ks : list Var) (aggs : list Aggregate)
  (values_of : list A -> SparqlExpr -> list (option Term)) (g : Key * list A)
  : FMapping :=
  key_mapping ks (fst g) ++ agg_bindings (values_of (snd g)) aggs.

(** ** Flat evaluation *)

Definition key_f (ks : list Var) (f : FMapping) : Key := key_of (lk_f f) ks.

Definition values_f (members : list FMapping) (e : SparqlExpr)
  : list (option Term) :=
  map (fun f => eval_expr (lk_f f) e) members.

Definition groupagg_flat (ks : list Var) (aggs : list Aggregate)
  (L : list FMapping) : list FMapping :=
  map (group_result ks aggs values_f) (groups (key_f ks) ks L).

(** ** Condensed evaluation (count-views, Definition 5.39) *)

Definition key_c (ks : list Var) (m : CMapping) : Key := key_of (lk_c m) ks.

(** Each condensed mapping contributes the value of the expression as many
    times as it has flat expansions. *)
Definition values_c (members : list CMapping) (e : SparqlExpr)
  : list (option Term) :=
  flat_map (fun m => repeat (eval_expr (lk_c m) e) (cardinality m)) members.

(** A flat mapping as a condensed mapping with ν bindings. *)
Definition to_vals (f : FMapping) : CMapping :=
  map (fun xt => (fst xt, BVal (snd xt))) f.

Definition groupagg_cond (ks : list Var) (aggs : list Aggregate)
  (M : list CMapping) : list CMapping :=
  map (fun g => to_vals (group_result ks aggs values_c g))
      (groups (key_c ks) ks M).

(** COUNT on a condensed group is the sum of the cardinalities of the
    mappings on which the expression is defined (Definition 5.39). *)
Lemma count_values_c : forall members e,
  count_values (values_c members e)
  = Some (term_of_nat
            (fold_right (fun m n =>
                           (if is_some (eval_expr (lk_c m) e) then cardinality m else 0)
                           + n) 0 members)).
Proof.
  intros members e. unfold count_values. f_equal. f_equal.
  induction members as [|m members IH]; simpl; [reflexivity|].
  rewrite filter_app, length_app, IH. f_equal.
  destruct (eval_expr (lk_c m) e) eqn:E; simpl.
  - induction (cardinality m) as [|n IHn]; simpl; [reflexivity | rewrite IHn; reflexivity].
  - apply length_zero_iff_nil. apply filter_false_In. intros o Ho.
    apply repeat_spec in Ho. subst o. reflexivity.
Qed.

(** ** Basic facts *)

Lemma map_flat_map_single : forall {A B : Type} (h : A -> B) l,
  map h l = flat_map (fun a => [h a]) l.
Proof.
  intros A B h l. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite IH. reflexivity.
Qed.

Lemma filter_map_ext_in : forall {A B : Type} (f g : A -> option B) l,
  (forall a, In a l -> f a = g a) -> filter_map f l = filter_map g l.
Proof.
  intros A B f g l H. unfold filter_map. apply flat_map_ext_in.
  intros a Ha. rewrite (H a Ha). reflexivity.
Qed.

Lemma in_combine_map : forall {A B : Type} (h : A -> B) (l : list A) a b,
  In (a, b) (combine l (map h l)) -> b = h a.
Proof.
  intros A B h l. induction l as [|a0 l IH]; simpl; intros a b H; [contradiction|].
  destruct H as [H | H]; [injection H as <- <-; reflexivity | apply IH; exact H].
Qed.

Lemma expand_to_vals : forall f, expand (to_vals f) = [f].
Proof.
  induction f as [|[x t] f IH]; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma to_vals_keys : forall f, keys (to_vals f) = keys f.
Proof. intros f. unfold to_vals, keys. rewrite map_map. reflexivity. Qed.

Lemma to_vals_lookup : forall f x,
  lookup x (to_vals f) = match lookup x f with Some t => Some (BVal t) | None => None end.
Proof.
  intros f x. unfold to_vals.
  rewrite (lookup_map_fst x (fun xt => BVal (snd xt)) f). reflexivity.
Qed.

Lemma to_vals_wf : forall f, NoDup (keys f) -> wf_cmap (to_vals f).
Proof.
  intros f H. split; [rewrite to_vals_keys; exact H|].
  apply Forall_forall. intros xb Hin. unfold to_vals in Hin.
  apply in_map_iff in Hin. destruct Hin as [xt [<- _]]. exact I.
Qed.

Lemma key_mapping_keys_incl : forall ks k x,
  In x (keys (key_mapping ks k)) -> In x ks.
Proof.
  intros ks k x Hx. unfold key_mapping, keys in Hx. apply in_map_iff in Hx.
  destruct Hx as [[y t] [<- Hin]]. apply in_filter_map in Hin.
  destruct Hin as [[y' o] [Hin Heq]]. cbn [fst snd] in Heq.
  destruct o; [|discriminate]. injection Heq as <- <-.
  apply in_combine_l in Hin. exact Hin.
Qed.

(** A grouping variable bound in the solution of a group whose key comes
    from a condensed mapping [m] is bound in [m]. *)
Lemma key_mapping_lookup_c : forall ks m x t,
  lookup x (key_mapping ks (key_c ks m)) = Some t -> lk_c m x = Some t.
Proof.
  intros ks m x t Hl. apply lookup_Some_In in Hl.
  unfold key_mapping, key_c, key_of in Hl. apply in_filter_map in Hl.
  destruct Hl as [[y o] [Hin Heq]]. cbn [fst snd] in Heq.
  destruct o; [|discriminate]. injection Heq as <- <-.
  apply in_combine_map in Hin. congruence.
Qed.

(** The keys of the group solution are duplicate-free when the grouping
    variables and the aggregate variables are. *)
Lemma NoDup_keys_key_mapping : forall ks k,
  NoDup ks -> NoDup (keys (key_mapping ks k)).
Proof.
  intros ks k Hnd. unfold key_mapping.
  revert k. induction ks as [|x ks IH]; intros k; [constructor|].
  apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  destruct k as [|o k]; [constructor|].
  unfold filter_map. cbn [combine flat_map snd fst].
  destruct o as [t|].
  - cbn [app keys map fst]. constructor; [|apply IH; exact Hnd].
    intros Hx. apply Hnotin.
    apply (key_mapping_keys_incl ks k x). exact Hx.
  - cbn [app]. apply IH. exact Hnd.
Qed.

Lemma agg_bindings_keys_incl : forall values aggs x,
  In x (keys (agg_bindings values aggs)) -> In x (map agg_var aggs).
Proof.
  intros values aggs x Hx. unfold agg_bindings, keys in Hx.
  apply in_map_iff in Hx. destruct Hx as [[y t] [<- Hin]].
  apply in_filter_map in Hin. destruct Hin as [ag [Hin Heq]].
  destruct (agg_apply _ _); [|discriminate]. injection Heq as <- <-.
  exact (in_map agg_var aggs ag Hin).
Qed.

Lemma NoDup_keys_agg_bindings : forall values aggs,
  NoDup (map agg_var aggs) -> NoDup (keys (agg_bindings values aggs)).
Proof.
  intros values aggs Hnd. unfold agg_bindings.
  induction aggs as [|ag aggs IH]; [constructor|].
  cbn [map] in Hnd. apply NoDup_cons_iff in Hnd. destruct Hnd as [Hnotin Hnd].
  unfold filter_map. cbn [flat_map]. destruct (agg_apply _ _) as [t|].
  - cbn [app keys map fst]. constructor; [|apply IH; exact Hnd].
    intros Hx. apply Hnotin. apply (agg_bindings_keys_incl values aggs). exact Hx.
  - cbn [app]. apply IH. exact Hnd.
Qed.

Lemma NoDup_keys_group_result : forall {A : Type} ks aggs values_of (g : Key * list A),
  NoDup ks -> NoDup (map agg_var aggs) ->
  (forall x, In x (map agg_var aggs) -> ~ In x ks) ->
  NoDup (keys (group_result ks aggs values_of g)).
Proof.
  intros A ks aggs values_of g Hks Haggs Hdisj. unfold group_result.
  rewrite keys_app. apply NoDup_app.
  - apply NoDup_keys_key_mapping. exact Hks.
  - apply NoDup_keys_agg_bindings. exact Haggs.
  - intros x Hx1 Hx2. apply (Hdisj x).
    + apply (agg_bindings_keys_incl _ _ _ Hx2).
    + apply (key_mapping_keys_incl _ _ _ Hx1).
Qed.

(** ** Keys are preserved by expansion (Lemma 6.3) *)

Lemma key_expand : forall ks m f,
  In f (expand m) -> point_on ks m -> key_f ks f = key_c ks m.
Proof.
  intros ks m f Hf Hp. unfold key_f, key_c, key_of. apply map_ext_in.
  intros x Hx. apply value_preservation; [exact Hf|].
  intros b Hb. apply (Hp x b Hx Hb).
Qed.

(** ** Values are preserved up to multiplicity (Lemma 6.7) *)

Lemma map_const_repeat : forall {A B : Type} (h : A -> B) (c : B) l,
  (forall a, In a l -> h a = c) -> map h l = repeat c (length l).
Proof.
  intros A B h c l H. induction l as [|a l IH]; simpl; [reflexivity|].
  rewrite (H a (or_introl eq_refl)), IH; [reflexivity|].
  intros a' Ha'. apply H. right. exact Ha'.
Qed.

Lemma values_perm : forall e M L,
  Forall (fun m => point_on (expr_vars e) m) M ->
  Permutation L (flat_map expand M) ->
  Permutation (values_f L e) (values_c M e).
Proof.
  intros e M L Hp HP. unfold values_f, values_c.
  etransitivity; [apply Permutation_map; exact HP|].
  rewrite map_flat_map. apply Permutation_refl'. apply flat_map_ext_in.
  intros m Hm. rewrite <- expand_length. apply map_const_repeat.
  intros f Hf. rewrite Forall_forall in Hp. apply eval_expr_expand; auto.
Qed.

(** ** Groups are preserved *)

Lemma flat_map_if_filter : forall {A B : Type} (q : A -> bool) (f : A -> list B) l,
  flat_map (fun a => if q a then f a else []) l = flat_map f (filter q l).
Proof.
  intros A B q f l. induction l as [|a l IH]; simpl; [reflexivity|].
  destruct (q a); simpl; rewrite IH; reflexivity.
Qed.

Lemma group_members_perm : forall ks M L k,
  Forall (fun m => point_on ks m) M ->
  Permutation L (flat_map expand M) ->
  Permutation (filter (fun f => key_eqb (key_f ks f) k) L)
              (flat_map expand (filter (fun m => key_eqb (key_c ks m) k) M)).
Proof.
  intros ks M L k Hp HP.
  etransitivity; [apply Permutation_filter; exact HP|].
  rewrite filter_flat_map, <- flat_map_if_filter.
  apply Permutation_refl'. apply flat_map_ext_in. intros m Hm.
  rewrite Forall_forall in Hp.
  destruct (key_eqb (key_c ks m) k) eqn:E.
  - apply filter_true_In. intros f Hf.
    rewrite (key_expand ks m f Hf (Hp m Hm)). exact E.
  - apply filter_false_In. intros f Hf.
    rewrite (key_expand ks m f Hf (Hp m Hm)). exact E.
Qed.

Lemma group_keys_perm : forall ks M L,
  Forall wf_cmap M ->
  Forall (fun m => point_on ks m) M ->
  Permutation L (flat_map expand M) ->
  Permutation (nodup Key_eq_dec (map (key_f ks) L))
              (nodup Key_eq_dec (map (key_c ks) M)).
Proof.
  intros ks M L Hwf Hp HP. apply NoDup_Permutation; try apply NoDup_nodup.
  intros k. rewrite !nodup_In, !in_map_iff. rewrite Forall_forall in Hwf, Hp. split.
  - intros [f [<- Hf]]. apply (Permutation_in _ HP) in Hf.
    apply in_flat_map in Hf. destruct Hf as [m [Hm Hf]].
    exists m. split; [symmetry; apply key_expand; auto | exact Hm].
  - intros [m [<- Hm]]. exists (witness_flat m). split.
    + apply key_expand; [|apply Hp; exact Hm].
      apply witness_flat_in_expand. apply wf_cmap_vals_nonempty. apply Hwf. exact Hm.
    + apply (Permutation_in _ (Permutation_sym HP)). apply in_flat_map.
      exists m. split; [exact Hm|].
      apply witness_flat_in_expand. apply wf_cmap_vals_nonempty. apply Hwf. exact Hm.
Qed.

(** ** GROUP / AGGREGATION case of Theorem 6.2 *)

Lemma flat_map_expand_nil : forall M,
  Forall wf_cmap M -> flat_map expand M = [] -> M = [].
Proof.
  intros [|m M] Hwf H; [reflexivity|]. exfalso.
  inversion Hwf as [| ? ? Hm _]; subst. simpl in H.
  apply app_eq_nil in H. destruct H as [H _].
  pose proof (witness_flat_in_expand m (wf_cmap_vals_nonempty m Hm)) as Hin.
  rewrite H in Hin. contradiction.
Qed.

Lemma groupagg_perm : forall ks aggs M L,
  Forall wf_cmap M ->
  Forall (fun m => point_on ks m) M ->
  Forall (fun m => Forall (fun ag => point_on (expr_vars (agg_expr ag)) m) aggs) M ->
  Permutation L (flat_map expand M) ->
  Permutation (groupagg_flat ks aggs L) (flat_map expand (groupagg_cond ks aggs M)).
Proof.
  intros ks aggs M L Hwf Hks Haggs HP. unfold groupagg_flat, groupagg_cond.
  rewrite flat_map_map_comp.
  rewrite (flat_map_ext _ (fun g => [group_result ks aggs values_c g]))
    by (intros g; apply expand_to_vals).
  rewrite <- (map_flat_map_single (group_result ks aggs values_c)).
  destruct L as [|f L'].
  - (* no solution: at most the implicit group *)
    assert (HM : M = []).
    { apply flat_map_expand_nil; [exact Hwf|]. apply Permutation_nil. exact HP. }
    subst M. destruct ks; reflexivity.
  - assert (HL : f :: L' <> []) by discriminate.
    assert (HM : M <> []).
    { intros ->. simpl in HP. apply Permutation_sym in HP.
      apply Permutation_nil in HP. discriminate. }
    rewrite (groups_nonempty _ ks (f :: L') HL), (groups_nonempty _ ks M HM).
    unfold group_by. rewrite !map_map.
    transitivity
      (map (fun k => group_result ks aggs values_c
                       (k, filter (fun m => key_eqb (key_c ks m) k) M))
           (nodup Key_eq_dec (map (key_f ks) (f :: L')))).
    + apply Permutation_refl'. apply map_ext_in. intros k Hk.
      unfold group_result. cbn [fst snd]. f_equal.
      unfold agg_bindings. apply filter_map_ext_in. intros ag Hag.
      rewrite (agg_apply_perm (agg_fun ag)
                 (values_f (filter (fun f' => key_eqb (key_f ks f') k) (f :: L'))
                           (agg_expr ag))
                 (values_c (filter (fun m => key_eqb (key_c ks m) k) M) (agg_expr ag)));
        [reflexivity|].
      apply values_perm.
      * apply Forall_forall. intros m Hm. apply filter_In in Hm.
        rewrite Forall_forall in Haggs. specialize (Haggs m (proj1 Hm)).
        rewrite Forall_forall in Haggs. apply Haggs. exact Hag.
      * apply group_members_perm; assumption.
    + apply Permutation_map. apply group_keys_perm; assumption.
Qed.
