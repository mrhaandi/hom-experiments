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




(* Left-to-right iterator on trees along a position.

 *)
Fixpoint map_tree (A : Type) (B : Type) (f : A -> B) (tr : rose_tree A)  : rose_tree B :=
  match tr with
  | node v ts => node (f v) (map (map_tree A B f) ts)
  end.

Arguments map_tree {A B}.




(* The replace in the tree tr the subtree at position p with tr'. *)
Fixpoint replace_subtree (A : Type) (tr : rose_tree A) (p: position) (tr' : rose_tree A) :=
  match p with
  | [] => tr'
  | hd :: tl => let 'node v children := tr in
                let pairs := combine (seq 0 (length children)) children in
                let mapping := fun  '(m, tr'') =>
                                 if m =? hd
                                 then replace_subtree A tr'' tl tr'
                                 else tr'' in
                node v (map mapping pairs)
  end.

Arguments replace_subtree {A}.

Lemma replace_subtree_nil:
  forall (A:Type) (tr : rose_tree A) tr',
    replace_subtree tr [] tr' = tr'.
Proof.
  intros.
  simpl.
  destruct tr.
  now simpl.
Qed.


Lemma nth_error_combine_map:
  forall A B C D (f : A -> B) (f' : (C*A) -> D) (l : list A) (l': list C) a e e',
    nth_error l a = Some e ->
    nth_error l' a = Some e' ->
    length l' = length l ->
    nth_error (map f' (combine l' l)) a = Some (f' (e',e)).
Proof.
  induction l.
  * intros.
    simpl in *.
    simpl.
    apply length_zero_iff_nil in H1.
    subst l'.
    simpl in *.
    rewrite nth_error_nil in H.
    congruence.
  * intros.
    destruct l'; simpl in H1;try congruence.
    destruct a0.
    ** simpl.
       simpl in H, H0.
       congruence.
    ** simpl in H, H0.
       simpl.
       eapply IHl in H;eauto.
Qed.

Lemma replace_subtree_decompose:
  forall A tl l l' (a:A) a' hd  tr tr'' tr3,
    replace_subtree (node a l) (hd :: tl) tr = node a' l' ->
    nth_error l hd = Some tr'' ->
    nth_error l' hd = Some tr3 ->
    replace_subtree tr'' tl tr = tr3.
Proof.
  admit.
Admitted.

  
Lemma replace_get_subtree:
  forall (A:Type)  p (tr : rose_tree A) tr' tr'' tr''',
    replace_subtree tr p tr' = tr'' ->
    get_subtree tr p = Some tr''' ->
    get_subtree tr'' p = Some tr'.
Proof.
  induction p.
  * intros.
    destruct tr.
    simpl in *.
    now subst tr'.
  * intros.
    admit.
Admitted.


(*
(* The replace in the tree tr the subtree at position p with tr'. *)
Fixpoint replace_subtree_acc (A B : Type)
  (facc : A -> B -> A) (ftr : A -> B -> B) (tr : rose_tree B) (p: position) (tr' : rose_tree B) (acc : A):=
  match p with
  | [] => Some (map_tree tr' (ftr acc) tr')
  | hd :: tl => let 'node v children := tr in
                let pairs := combine (seq 0 (length children)) children in
                let mapping := fun  in
                                    
                in match nth_error children hd with
                   | Some tr'' => replace_subtree_acc A tr'' tl tr'
                   | None => None
                   end
  end.
*)
