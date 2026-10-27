(** * The small solution theorem and decidability  [S, Thm. 37]

    [Thm37] is the statement of [S, Thm. 37].  It is not proved here: its
    proof in the paper rests on Gaps 1-5 of the notes (T2, Prop. 32,
    partition tree, unfolding, counting).  We prove that it implies the
    decidability of interpolation (hence of matching, [S, Prop. 5]). *)

From Coq Require Import List Arith Bool Lia.
From HOM Require Import Syntax Lambda Transform.
Import ListNotations.

(** ** The bound *)

Fixpoint fo_arities (r : fo) : list nat :=
  match r with FApp _ l => length l :: flat_map fo_arities l end.

(** [q] bounds the arity of [E] and of the constants of [u] (the paper
    uses the arity of [E] only; constant nodes branch according to the
    constants of [u]). *)
Definition q_of (E : ieq) : nat :=
  Nat.max (ar (eq_ty E)) (list_max (fo_arities (eq_goal E))).

(** [E] has order [2p] or [2p+1]. *)
Definition p_of (E : ieq) : nat := ord (eq_ty E) / 2.

Definition bound (E : ieq) : nat :=
  let p := p_of E in let q := q_of E in
  4 * (p * p) * q ^ (2 * p - 2) * fo_size (eq_goal E).

(** [S, Thm. 37] (depth counts the nodes of the tree, dummy lambdas
    included, as in the paper's tree representation). *)
Definition Thm37 : Prop :=
  forall E, wf_eq E -> solvable E ->
    exists t, solution E t /\ depth t <= bound E.

(** ** Enumerating the candidates of bounded depth *)

Definition var_heads (G : ctx) : list head :=
  flat_map (fun k => map (HVar k) (seq 0 (length (nth k G []))))
           (seq 0 (length G)).

Definition heads (G : ctx) (C : list cst) : list head :=
  var_heads G ++ map HCst C.

Fixpoint prod (ls : list (list lnf)) : list (list lnf) :=
  match ls with
  | [] => [[]]
  | l :: ls' => flat_map (fun a => map (cons a) (prod ls')) l
  end.

Fixpoint enum (d : nat) (G : ctx) (C : list cst) (A : ty) : list lnf :=
  match d with
  | S (S d') =>
      match A with
      | Ty As =>
          flat_map (fun h =>
            match head_ty (As :: G) h with
            | Some (Ty Bs) => map (Lam As h) (prod (map (enum d' (As :: G) C) Bs))
            | None => []
            end) (heads (As :: G) C)
      end
  | _ => []
  end.

Lemma prod_complete : forall args ls,
  Forall2 (fun a l => In a l) args ls -> In args (prod ls).
Proof.
  intros args ls H. induction H as [|a l args ls Ha H IH]; simpl; auto.
  apply in_flat_map. exists a. split; auto. now apply in_map.
Qed.

Lemma heads_complete : forall G C h B, head_ty G h = Some B ->
  (forall c, h = HCst c -> In c C) -> In h (heads G C).
Proof.
  intros G C [k i|c] B Hh Hc; unfold heads; apply in_or_app.
  - left. simpl in Hh.
    destruct (nth_error G k) as [As|] eqn:Hk; [|discriminate].
    unfold var_heads. apply in_flat_map. exists k. split.
    + apply in_seq. assert (Hk' : nth_error G k <> None) by congruence.
      apply nth_error_Some in Hk'. lia.
    + apply in_map. apply in_seq.
      rewrite (nth_error_nth G k [] Hk).
      assert (nth_error As i <> None) by congruence.
      apply nth_error_Some in H. simpl. lia.
  - right. apply in_map. now apply Hc.
Qed.

Theorem enum_complete : forall d G C t A,
  wt G t A = true -> depth t <= d -> incl (consts t) C -> In t (enum d G C A).
Proof.
  induction d as [d IH] using lt_wf_ind.
  intros G C [As h args] A Hwt Hd Hc.
  apply wt_Lam in Hwt. destruct Hwt as [-> [Bs [Hh Hargs]]].
  simpl in Hd. destruct d as [|[|d']]; try lia.
  assert (Hall : forall a, In a args -> depth a <= d' /\ incl (consts a) C).
  { intros a Ha. split.
    - pose proof (list_max_ge (map depth args) (depth a) (in_map _ _ _ Ha)). lia.
    - intros c Hca. apply Hc. simpl. apply in_or_app. right.
      apply in_flat_map. eauto. }
  simpl. apply in_flat_map. exists h. split.
  - apply heads_complete with (Ty Bs); auto.
    intros c ->. apply Hc. simpl. now left.
  - rewrite Hh. apply in_map. apply prod_complete.
    clear Hh Hd Hc.
    induction Hargs as [|a B args Bs Ha Hrest IHr]; simpl; constructor.
    + apply IH; [lia|exact Ha|apply Hall; now left|apply Hall; now left].
    + apply IHr. intros a' Ha'. apply Hall. now right.
Qed.

(** ** Decidability *)

Theorem decidable_interpolation : Thm37 ->
  forall E, wf_eq E -> {solvable E} + {~ solvable E}.
Proof.
  intros H37 E Hwf.
  destruct (Exists_dec (solution E) (enum (bound E) [] (CE E) (eq_ty E))
              (solution_dec E)) as [Hex|Hnex].
  - left. apply Exists_exists in Hex. destruct Hex as [t [_ Ht]]. now exists t.
  - right. intros Hs. destruct (H37 E Hwf Hs) as [t [Ht Hd]].
    apply Hnex. apply Exists_exists. exists t. split; auto.
    destruct Ht as [[Hc _] Hce].
    apply enum_complete; auto.
Qed.
