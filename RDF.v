(** * RDF: Core RDF Type Definitions
    
    This module defines the fundamental RDF types used throughout
    the ConVerG formalization, following W3C RDF 1.1 Concepts.
*)

From Stdlib Require Import Ensembles.
From Stdlib Require Import List.
Import ListNotations.

(** ** Basic Types *)

(** Literals denote resources of the real world. *)
Parameter Literal : Type.
Parameter Literal_eq_dec : forall l1 l2 : Literal, {l1 = l2} + {l1 <> l2}.

(** IRIs (Internationalized Resource Identifiers) identify resources. *)
Parameter IRI : Type.
Parameter IRI_eq_dec : forall i1 i2 : IRI, {i1 = i2} + {i1 <> i2}.

(** Terms are either IRIs or Literals. *)
Inductive Term : Type :=
  | TermIRI : IRI -> Term
  | TermLit : Literal -> Term.

Definition Term_eq_dec : forall t1 t2 : Term, {t1 = t2} + {t1 <> t2}.
Proof.
  intros t1 t2.
  destruct t1 as [i1 | l1]; destruct t2 as [i2 | l2].
  - destruct (IRI_eq_dec i1 i2) as [Heq | Hneq].
    + left. rewrite Heq. reflexivity.
    + right. intros H. injection H. intros. contradiction.
  - right. discriminate.
  - right. discriminate.
  - destruct (Literal_eq_dec l1 l2) as [Heq | Hneq].
    + left. rewrite Heq. reflexivity.
    + right. intros H. injection H. intros. contradiction.
Defined.

(** ** RDF Structures *)

(** An RDF triple consists of subject, predicate, and object. *)
Record Triple : Type := mkTriple {
  subject : IRI;
  predicate : IRI;
  object : Term
}.

(** An RDF quad extends a triple with a named graph identifier. *)
Record Quad : Type := mkQuad {
  quad_subject : IRI;
  quad_predicate : IRI;
  quad_object : Term;
  quad_graph : IRI
}.

(** Extract a triple from a quad. *)
Definition quad_to_triple (q : Quad) : Triple :=
  mkTriple (quad_subject q) (quad_predicate q) (quad_object q).

(** ** Named Graphs *)

(** The set of all named graphs is a subset of IRIs. *)
Definition NamedGraphs := Ensemble IRI.

(** ** Variables *)

(** SPARQL variables are represented as natural numbers for simplicity. *)
Definition Var := nat.
Definition Var_eq_dec := PeanoNat.Nat.eq_dec.

(** ** Finite Sets *)

(** We use lists to represent finite sets in this formalization. *)
Definition FiniteSet (A : Type) := list A.

Definition empty_set {A : Type} : FiniteSet A := [].

Definition singleton {A : Type} (x : A) : FiniteSet A := [x].

Definition set_union {A : Type} (s1 s2 : FiniteSet A) : FiniteSet A := s1 ++ s2.

Definition set_member {A : Type} (eq_dec : forall x y : A, {x = y} + {x <> y}) 
                      (x : A) (s : FiniteSet A) : bool :=
  existsb (fun y => if eq_dec x y then true else false) s.

(** ** Domain Function *)

(** Domain of a partial function represented as an association list. *)
Definition domain {A B : Type} (f : list (A * B)) : list A :=
  map fst f.
