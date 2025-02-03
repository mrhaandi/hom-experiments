Require Import List ssreflect.
Import ListNotations.
Require Import PeanoNat.
Require Import Nat.
Require Import Lia.



Inductive rose_tree (A : Type) : Type :=
| node : A -> list (rose_tree A) -> rose_tree A.

Arguments node {A}.


(* Positions in a tree or term are lists of natural numbers. *)
Definition position := list nat.


(* The depth of a tree. *)
Fixpoint get_tdepth (A : Type) (tr: rose_tree A) :=
  match tr with
  | node v children => fold_left (fun acc el => let nacc := (get_tdepth A el) in
                                                match (acc ?= nacc)  with
                                                | Eq => acc
                                                | Lt => nacc
                                                | Gt => acc
                                                end) children 0%nat
  end.

Arguments get_tdepth {A}.


(* The subtree of tr at position p. *)
Fixpoint get_subtree (A : Type) (tr : rose_tree A) (p: position) :=
  match p with
  | [] => Some tr
  | hd :: tl => let 'node v children := tr
                in match nth_error children hd with
                   | Some tr' => get_subtree A tr' tl
                   | None => None
                   end
  end.

Arguments get_subtree {A}.


(* Left-to-right iterator on trees along a position.

 *)
Fixpoint fold_left_tree (A : Type) (B : Type) (f : A -> B -> A) (tr : rose_tree B) (p : position) (aggr : A) : option A :=
  match tr, p with
  | node _ _, [] => Some aggr
  | node v ts, i :: p =>
    match nth_error ts i with
    | Some ti => fold_left_tree A B f ti p (f aggr v)
    | None => None
    end
  end.


Arguments fold_left_tree {A B}.


Lemma fold_left_tree_app : forall (A B : Type) f (p p':position) (tr tr': rose_tree B)  (a a':A),
    get_subtree tr p = Some tr' ->
    fold_left_tree f tr p a = Some a' ->
    fold_left_tree f tr (p++p') a = fold_left_tree f tr' p' a'.
Proof.
  induction p.
  * intros.
    simpl in *.
    destruct tr.
    congruence.
  * intros.
    simpl in H.
    simpl in H0.
    simpl.               
    destruct tr.
    destruct (nth_error l a) eqn:Nth.
    ** eapply IHp in H;eauto.
    ** congruence.
Qed.

Lemma fold_left_tree_S_k :
  forall (A : Type)   (p:position) (tr tr' : rose_tree A) (k : nat),
    get_subtree tr p = Some tr' ->
    fold_left_tree (fun x _ => S x) tr p k = Some (k + (length p)).
Proof.
  induction p.
  * intros.
    simpl in *.
    destruct tr. 
    now replace (k+0) with k by lia.
  * intros.
    destruct tr.
    simpl in *.
    destruct (nth_error l a); try congruence.
    replace (k + S (length p)) with ((S k) + (length p)) by lia.
    eauto.
Qed.

Lemma fold_left_tree_S_0 :
  forall (A : Type)   (p:position) (tr tr' : rose_tree A),
    get_subtree tr p = Some tr' ->
    fold_left_tree (fun x _ => S x) tr p 0 = Some (length p).
Proof.
  intros.
  eauto using fold_left_tree_S_k.
Qed.
