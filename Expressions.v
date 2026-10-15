(** * Expressions: SPARQL Expressions and Conditions

    Thesis, Section 5.2 (expressions used by FILTER, BIND, and the
    conditions of DIFF and OPTIONAL).

    Expressions are evaluated against a partial lookup function
    [Var -> option Term], so that the same evaluator is used on flat
    mappings ([lk_f]) and on condensed mappings ([lk_c]).  The semantics
    of built-in functions and of the effective boolean value are left
    abstract: they are the same in both algebras, which is all that the
    equivalence theorem needs.
*)

From Stdlib Require Import List Bool.
Require Import ConVerG.RDF.
Require Import ConVerG.ListUtil.
Require Import ConVerG.Versioning.
Require Import ConVerG.Representations.
Require Import ConVerG.SolutionMappings.
Import ListNotations.

(** ** Syntax *)

Inductive SparqlExpr : Type :=
  | ExprTerm : Term -> SparqlExpr            (** constant *)
  | ExprVar : Var -> SparqlExpr              (** variable *)
  | ExprBound : Var -> SparqlExpr            (** BOUND(?x) *)
  | ExprFunc : nat -> list SparqlExpr -> SparqlExpr.
                                             (** built-in or user function *)

(** Induction principle with a [Forall] hypothesis for the arguments of
    a function application (the generated one is too weak). *)
Section SparqlExpr_ind'.
  Variable P : SparqlExpr -> Prop.
  Hypothesis HTerm : forall t, P (ExprTerm t).
  Hypothesis HVar : forall x, P (ExprVar x).
  Hypothesis HBound : forall x, P (ExprBound x).
  Hypothesis HFunc : forall n args, Forall P args -> P (ExprFunc n args).

  Fixpoint SparqlExpr_ind' (e : SparqlExpr) : P e :=
    match e with
    | ExprTerm t => HTerm t
    | ExprVar x => HVar x
    | ExprBound x => HBound x
    | ExprFunc n args =>
        HFunc n args
          ((fix F (l : list SparqlExpr) : Forall P l :=
              match l with
              | [] => @Forall_nil _ P
              | e' :: l' => @Forall_cons _ P e' l' (SparqlExpr_ind' e') (F l')
              end) args)
    end.
End SparqlExpr_ind'.

(** ** Abstract semantics of functions and booleans *)

(** Interpretation of the function with code [n] on evaluated arguments;
    [None] is the SPARQL error value. *)
Parameter interp_func : nat -> list Term -> option Term.

(** Effective boolean value of a term ([None]: type error). *)
Parameter ebv : Term -> option bool.

(** The boolean literals. *)
Parameter term_of_bool : bool -> Term.

(** ** Evaluation *)

(** All-or-nothing collection of evaluated arguments. *)
Fixpoint sequence {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | Some a :: l' => match sequence l' with
                    | Some l'' => Some (a :: l'')
                    | None => None
                    end
  | None :: _ => None
  end.

Fixpoint eval_expr (lk : Var -> option Term) (e : SparqlExpr) : option Term :=
  match e with
  | ExprTerm t => Some t
  | ExprVar x => lk x
  | ExprBound x =>
      Some (term_of_bool (match lk x with Some _ => true | None => false end))
  | ExprFunc n args =>
      match sequence (map (eval_expr lk) args) with
      | Some ts => interp_func n ts
      | None => None
      end
  end.

(** Variables occurring in an expression. *)
Fixpoint expr_vars (e : SparqlExpr) : list Var :=
  match e with
  | ExprTerm _ => []
  | ExprVar x => [x]
  | ExprBound x => [x]
  | ExprFunc _ args => flat_map expr_vars args
  end.

(** Evaluation only depends on the lookup of the variables of the
    expression. *)
Lemma eval_expr_ext : forall e lk1 lk2,
  (forall x, In x (expr_vars e) -> lk1 x = lk2 x) ->
  eval_expr lk1 e = eval_expr lk2 e.
Proof.
  induction e as [t | x | x | n args IHargs] using SparqlExpr_ind';
    intros lk1 lk2 H; simpl.
  - reflexivity.
  - apply H. left. reflexivity.
  - rewrite (H x) by (left; reflexivity). reflexivity.
  - assert (Hargs : map (eval_expr lk1) args = map (eval_expr lk2) args).
    { apply map_ext_in. intros a Ha. rewrite Forall_forall in IHargs.
      apply (IHargs a Ha). intros x Hx. apply H. apply in_flat_map.
      exists a. auto. }
    rewrite Hargs. reflexivity.
Qed.

(** ** Conditions *)

(** A condition holds when the expression evaluates, without error, to a
    term whose effective boolean value is [true]. *)
Definition cond_holds (lk : Var -> option Term) (c : SparqlExpr) : bool :=
  match eval_expr lk c with
  | Some t => match ebv t with Some true => true | _ => false end
  | None => false
  end.

Lemma cond_holds_ext : forall c lk1 lk2,
  (forall x, In x (expr_vars c) -> lk1 x = lk2 x) ->
  cond_holds lk1 c = cond_holds lk2 c.
Proof.
  intros c lk1 lk2 H. unfold cond_holds. rewrite (eval_expr_ext c lk1 lk2 H).
  reflexivity.
Qed.

(** Consequence of Lemma 6.3 (Value Preservation): when the variables of
    an expression are point-valued in a condensed mapping, the expression
    has the same value on the condensed mapping and on each of its
    expansions. *)
Lemma eval_expr_expand : forall c m f,
  In f (expand m) -> point_on (expr_vars c) m ->
  eval_expr (lk_f f) c = eval_expr (lk_c m) c.
Proof.
  intros c m f Hf Hp. apply eval_expr_ext. intros x Hx.
  apply value_preservation; [exact Hf|]. intros b Hb. apply (Hp x b Hx Hb).
Qed.

Lemma cond_holds_expand : forall c m f,
  In f (expand m) -> point_on (expr_vars c) m ->
  cond_holds (lk_f f) c = cond_holds (lk_c m) c.
Proof.
  intros c m f Hf Hp. unfold cond_holds.
  rewrite (eval_expr_expand c m f Hf Hp). reflexivity.
Qed.
