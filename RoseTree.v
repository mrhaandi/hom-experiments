Require Import List ssreflect.
Import ListNotations.
Require Import PeanoNat.
Require Import Nat.
Require Import Lia.

Inductive rose_tree (A : Type) : Type :=
  | node : A -> list (rose_tree A) -> rose_tree A.

Arguments node {A}.

Fixpoint rose_tree_size {A : Type} (tr : rose_tree A) : nat :=
  match tr with
  | node _ ts => 1 + list_sum (map rose_tree_size ts)
  end.

(* induction principle on rose trees *)
Lemma rose_tree_ind' {A : Type} (P : rose_tree A -> Prop) :
  (forall (v : A) (l : list (rose_tree A)), Forall P l -> P (node v l)) ->
  forall tr, P tr.
Proof.
  move=> H. elim /(Nat.measure_induction _ (@rose_tree_size A)).
  move=> [v children] IH. apply: H.
  elim: children IH.
  - by constructor.
  - move=> ?? IH IH'. constructor.
    + apply: IH'=> /=. lia.
    + apply: IH => /= *. apply: IH'=> /=. lia.
Qed.

(* Positions in a tree or term are lists of natural numbers. *)
Definition position := list nat.

(* fold a tree with the function f taking
    the nodes on the path the the current node,
    the value of the current node,
    and the results of the children *)
(* TODO: should the order be reversed? (fun l => f (l ++ [v])) *)
(* TODO: should the position be an additional argument? *)
Fixpoint fold_tree_dependent {A B : Type} (f : list A -> A -> list B -> B) (tr : rose_tree A) : B :=
  match tr with
  | node v children => f [] v (map (fold_tree_dependent (fun l => f (v :: l))) children)
  end.

Definition fold_tree {A B : Type} (f : A -> list B -> B) (tr : rose_tree A) : B :=
  fold_tree_dependent (fun _ => f) tr.

Definition map_tree_dependent {A B : Type} (f : list A -> A -> B) (tr : rose_tree A) : rose_tree B :=
  fold_tree_dependent (fun l v ts => node (f l v) ts) tr.

Definition map_tree {A B : Type} (f : A -> B) (tr : rose_tree A) : rose_tree B :=
  map_tree_dependent (fun _ => f) tr.

(* The depth of a tree. *)
Definition get_tree_depth {A : Type} (tr: rose_tree A) :=
  fold_tree (fun _ results => list_max (map S results)) tr.

Definition get_value {A : Type} (tr : rose_tree A) : A :=
  match tr with
  | node v _ => v
  end.

Definition get_children {A : Type} (tr : rose_tree A) : list (rose_tree A) :=
  match tr with
  | node _ children => children
  end.

(* test whether the tree tr has position p *)
Fixpoint has_position {A : Type} (tr : rose_tree A) (p : position) : bool :=
  match p with
  | [] => true
  | hd :: tl =>
    match nth_error (get_children tr) hd with
    | Some tr' => has_position tr' tl
    | None => false
    end
  end.

(* The subtree of tr at legal position p. *)
Fixpoint get_subtree {A : Type} (tr : rose_tree A) (p : position) : rose_tree A :=
  match p with
  | [] => tr
  | hd :: tl =>
    match nth_error (get_children tr) hd with
    | Some tr' => get_subtree tr' tl
    | None => tr
    end
  end.

(* Give a list of node values along a path to a position *)
(* this can be computed simpler ad hoc, but I wanted to test dependent lemmas *)
Definition get_branch {A : Type} (tr : rose_tree A) (p : position) : list A :=
  get_value (get_subtree (map_tree_dependent (fun l v => l) tr) p).

(* map only the nth element of a list *)
Fixpoint map_nth {A : Type} (f : A -> A) (n : nat) (l : list A) : list A :=
  match l with
  | [] => []
  | hd :: tl =>
    match n with
    | 0 => f hd :: tl
    | S n' => hd :: map_nth f n' tl
    end
  end.

(* Replace the subtree of tr at position p with tr'. *)
Fixpoint replace_subtree {A : Type} (tr' : rose_tree A) (p : position) (tr : rose_tree A) :=
  match p with
  | [] => tr'
  | hd :: tl =>
    let 'node v children := tr in
    node v (map_nth (replace_subtree tr' tl) hd children)
  end.

Lemma replace_subtree_nil:
  forall (A:Type) (tr : rose_tree A) tr',
    replace_subtree tr' [] tr = tr'.
Proof.
  reflexivity.
Qed.

Lemma nth_error_map_nth_eq {A : Type} (l : list A) n f :
  nth_error (map_nth f n l) n = option_map f (nth_error l n).
Proof.
  elim: l n.
  - by case.
  - move=> ?? IH [|n]; first done.
    by apply: IH.
Qed.

Lemma replace_get_subtree {A : Type} p (tr : rose_tree A) tr' tr'' :
  replace_subtree tr' p tr = tr'' ->
  has_position tr p = true ->
  get_subtree tr'' p = tr'.
Proof.
  elim: p tr tr' tr''.
  * by move=> > <-.
  * move=> hd ? IH /= [? children] tr' [??] [] _ <- /=.
    rewrite nth_error_map_nth_eq.
    case E: (nth_error children hd) => [?|//].
    by apply: IH.
Qed.

Lemma replace_subtree_decompose {A : Type} tl l l' (a:A) a' hd  tr tr'' tr3 :
  replace_subtree tr (hd :: tl) (node a l) = node a' l' ->
  nth_error l hd = Some tr'' ->
  nth_error l' hd = Some tr3 ->
  replace_subtree tr tl tr'' = tr3.
Proof.
  move=> [] _ <- E.
  rewrite nth_error_map_nth_eq E.
  by case.
Qed.

Lemma get_branch_nil {A:Type} (tr : rose_tree A) :
  get_branch tr [] = [].
Proof.
  by case: tr.
Qed.

Lemma map_tree_node {A B : Type} (f : A -> B) v children :
  map_tree f (node v children) = node (f v) (map (map_tree f) children).
Proof.
  reflexivity.
Qed.

Lemma map_tree_dependent_node {A B : Type} (f : list A -> A -> B) v children :
  map_tree_dependent f (node v children) = node (f [] v) (map (map_tree_dependent (fun l => f (v :: l))) children).
Proof.
  reflexivity.
Qed.

Lemma map_tree_map_tree_dependent {A B C : Type} (f : list A -> A -> B) (g : B -> C) (tr : rose_tree A) :
  map_tree g (map_tree_dependent f tr) = map_tree_dependent (fun l a => g (f l a)) tr.
Proof.
  elim /(@rose_tree_ind' A): tr f.
  move=> v children IH f /=.
  rewrite !map_tree_dependent_node map_tree_node. congr node.
  rewrite map_map. apply: map_ext_Forall.
  apply: Forall_impl IH.
  by move=> rt ->.
Qed.

Lemma get_subtree_map_tree {A B : Type} (f : A -> B) (tr : rose_tree A) (p : position) :
  get_subtree (map_tree f tr) p = map_tree f (get_subtree tr p).
Proof.
  elim: p tr.
  - by case.
  - move=> hd p IH [v children] /=.
    rewrite nth_error_map.
    case E: (nth_error children hd) => [? /=|//].
    by rewrite IH.
Qed.

(* example of a difficult lemma for fold_tree_dependent *)
Lemma get_branch_cons {A : Type} (tr : rose_tree A) hd (tl : position) :
  get_branch tr (hd :: tl) =
  match nth_error (get_children tr) hd with
  | Some tr' => get_value tr :: get_branch tr' tl
  | None => []
  end.
Proof.
  rewrite /get_branch.
  move: tr => [v children] /=.
  rewrite nth_error_map.
  case: (nth_error children hd)=> [tr' /=|//].
  change (fold_tree_dependent (fun l _ ts => node (v :: l) ts) tr') with
    (map_tree_dependent (fun l _ => (v :: l)) tr').
  rewrite -map_tree_map_tree_dependent get_subtree_map_tree.
  by case: (get_subtree _ _).
Qed.

Lemma get_branch_app {A : Type} (p p' : position) (tr : rose_tree A) :
  has_position tr p = true ->
  get_branch tr (p ++ p') = get_branch tr p ++ get_branch (get_subtree tr p) p'.
Proof.
  elim: p tr.
  - move=> /= ? _.
    by rewrite get_branch_nil.
  - move=> ?? IH /= [??] /=.
    move E: (nth_error _ _) => [?|//].
    rewrite !get_branch_cons /= E.
    by move=> /IH ->.
Qed.

Lemma get_branch_length (A : Type) (p:position) (tr : rose_tree A) :
  has_position tr p = true ->
  length (get_branch tr p) = length p.
Proof.
  elim: p tr.
  - move=> ? /=.
    by rewrite get_branch_nil.
  - move=> ?? IH [??] /=.
    move E: (nth_error _ _) => [?|//].
    move=> /IH <-.
    by rewrite get_branch_cons /= E.
Qed.

(* experiments, just to see if it works *)



(* The subtree of tr at position p. *)

(* Left-to-right iterator on trees along a position.
now it is: fold of get_branch

Fixpoint fold_left_tree (A : Type) (B : Type) (f : A -> B -> A) (tr : rose_tree B) (p : position) (aggr : A) : option A :=
  match tr, p with
  | node _ _, [] => Some aggr
  | node v ts, i :: p =>
    match nth_error ts i with
    | Some ti => fold_left_tree A B f ti p (f aggr v)
    | None => None
    end
  end.
 *)


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
