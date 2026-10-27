(** * Locality of the game and the transformation T1  [S, Section 6.2] *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax Lambda ITree Game GameLemmas.
Import ListNotations.

(** ** Lists *)

Lemma update_nth_length : forall {A} i (f : A -> A) l,
  length (update_nth i f l) = length l.
Proof. intros A i f l. revert i. induction l; intros [|i]; simpl; auto. Qed.

Lemma nth_error_update_nth_eq : forall {A} i (f : A -> A) l,
  nth_error (update_nth i f l) i = option_map f (nth_error l i).
Proof. intros A i f l. revert i. induction l; intros [|i]; simpl; auto. Qed.

Lemma nth_error_update_nth_neq : forall {A} i j (f : A -> A) l, i <> j ->
  nth_error (update_nth i f l) j = nth_error l j.
Proof.
  intros A i j f l. revert i j. induction l; intros [|i] [|j] H; simpl; auto.
  congruence.
Qed.

(** ** Labels are preserved outside the replaced subtree *)

Lemma repl_binders : forall t p h' a',
  match repl t p h' a', t with Lam As' _ _, Lam As _ _ => As' = As end.
Proof.
  intros [As h args] p h' a'. destruct p as [|[|[|x]] p]; simpl; auto.
  destruct p as [|[|i] p]; simpl; auto.
Qed.

Lemma above_cons : forall x p q, above (x :: p) (x :: q) <-> above p q.
Proof.
  intros x p q. split; intros [w Hw]; exists w; [now inversion Hw|simpl; now f_equal].
Qed.

Lemma walk_repl : forall p t h' a' q, ~ above p q ->
  ilabel (walk (ILam (repl t p h' a')) q) = ilabel (walk (ILam t) q).
Proof.
  intro p. induction p as [p IH] using (well_founded_induction
    (Wf_nat.well_founded_ltof _ (@length nat))).
  intros [As h args] h' a' q Hab.
  destruct q as [|x q].
  - (* the lambda node itself *)
    pose proof (repl_binders (Lam As h args) p h' a') as HB.
    destruct (repl (Lam As h args) p h' a') as [As' h0 args0].
    simpl. now subst.
  - simpl. destruct (x =? 1) eqn:Hx; [|reflexivity].
    apply Nat.eqb_eq in Hx. subst x.
    destruct p as [|[|[|y]] p].
    + exfalso. apply Hab. now exists (1 :: q).
    + (* p starts with 0: no change *) reflexivity.
    + destruct p as [|[|i] p].
      * exfalso. apply Hab. now exists q.
      * reflexivity.
      * (* p = 1 :: S i :: p *)
        simpl. destruct q as [|z q].
        -- simpl. now rewrite update_nth_length.
        -- simpl. destruct (z =? 0) eqn:Hz; [reflexivity|].
           destruct (Nat.eq_dec (z - 1) i) as [Hzi|Hzi].
           ++ subst i. rewrite nth_error_update_nth_eq.
              destruct (nth_error args (z - 1)) as [a|] eqn:Ha; [|reflexivity].
              simpl. apply IH.
              ** unfold Wf_nat.ltof. simpl. lia.
              ** intro Hab'. apply Hab. destruct Hab' as [w Hw].
                 exists w. subst q. simpl. apply Nat.eqb_neq in Hz.
                 do 2 f_equal. lia.
           ++ rewrite nth_error_update_nth_neq by congruence. reflexivity.
    + reflexivity.
Qed.

Lemma label_at_replace : forall E t p s n, ~ above (1 :: p) n ->
  label_at E (replace t (1 :: p) s) n = label_at E t n.
Proof.
  intros E t p [Bs h' a'] n Hab. unfold replace, label_at, item_at, comps.
  destruct n as [|j q]; [reflexivity|].
  destruct (j =? 0) eqn:Hj; [reflexivity|].
  destruct (Nat.eq_dec j 1) as [->|Hj1].
  - simpl.
    pose proof (walk_repl p t h' a' q) as HW.
    assert (Hq : ~ above p q) by (intro H; apply Hab, above_cons, H).
    specialize (HW Hq).
    destruct (walk (ILam (repl t p h' a')) q) as [it|];
      destruct (walk (ILam t) q) as [it'|]; simpl in *; congruence.
  - destruct j as [|[|j]]; [discriminate|congruence|reflexivity].
Qed.

(** ** Locality  (Lemma "locality" of the notes)
    The move from a position depends only on the label at its node. *)

Lemma step_label : forall E t t' p,
  label_at E t (pnode p) = label_at E t' (pnode p) -> step E t p = step E t' p.
Proof. intros E t t' p H. unfold step. now rewrite H. Qed.

Lemma P_app : forall E (l l' : list pos) i, i < length l -> P E (l ++ l') i = P E l i.
Proof. intros. unfold P. now apply app_nth1. Qed.

Lemma P_firstn : forall E (l : list pos) m i, i < m -> P E (firstn m l) i = P E l i.
Proof.
  intros E l m i H. unfold P. revert m i H.
  induction l as [|x l IH]; intros [|m] [|i] H; simpl; try lia; auto.
  all: apply IH; lia.
Qed.

Theorem locality : forall E t t', WF E t ->
  (forall pi j, play E t pi -> j < length pi ->
     label_at E t (nd E pi j) = label_at E t' (nd E pi j)) ->
  forall pi, play E t' pi <-> play E t pi.
Proof.
  intros E t t' HWF Hagree pi. split.
  - intros [[H0 Hs] Hf].
    assert (Hpre : forall m, m < length pi -> run E t (firstn (S m) pi)).
    { induction m as [|m IHm]; intro Hm.
      - split.
        + destruct pi; [discriminate|exact H0].
        + intros i Hi. rewrite firstn_length in Hi. lia.
      - specialize (IHm ltac:(lia)).
        assert (Hne : firstn (S m) pi <> []).
        { destruct pi; [simpl in Hm; lia|discriminate]. }
        destruct (run_extends E t _ HWF IHm Hne) as [pi' Hpl].
        assert (Hlen : length (firstn (S m) pi) = S m)
          by (rewrite firstn_length; lia).
        assert (Hag : label_at E t (pnode (P E pi m)) = label_at E t' (pnode (P E pi m))).
        { pose proof (Hagree _ m Hpl) as HA.
          unfold nd in HA. rewrite P_app, P_firstn in HA by lia.
          apply HA. rewrite app_length. lia. }
        split.
        + destruct pi; [discriminate|exact H0].
        + intros i Hi. rewrite firstn_length in Hi.
          rewrite !P_firstn by lia.
          destruct (Nat.eq_dec i m) as [->|Him].
          * rewrite step_label with (t' := t') by exact Hag. apply Hs. lia.
          * destruct IHm as [_ IHs]. specialize (IHs i ltac:(lia)).
            rewrite !P_firstn in IHs by lia. exact IHs. }
    split; [|exact Hf].
    destruct pi as [|x pi0]; [discriminate|].
    specialize (Hpre (length pi0) ltac:(simpl; lia)).
    rewrite firstn_all2 in Hpre by (simpl; lia). exact Hpre.
  - intros Hpl. pose proof Hpl as [[H0 Hs] Hf]. split; [split|exact Hf].
    + exact H0.
    + intros i Hi. rewrite <- step_label with (t := t).
      * now apply Hs.
      * apply Hagree; auto. lia.
Qed.

(** ** Typing of long normal forms *)

Lemma wt_Lam : forall G As h args A,
  wt G (Lam As h args) A = true <->
  A = Ty As /\ exists Bs, head_ty (As :: G) h = Some (Ty Bs) /\
    Forall2 (fun a B => wt (As :: G) a B = true) args Bs.
Proof.
  intros G As h args A. simpl. rewrite andb_true_iff, ty_eqb_eq.
  destruct (head_ty (As :: G) h) as [[Bs]|].
  - match goal with |- context [?F args Bs] => set (go := F) end.
    assert (Hgo : forall l Bs', go l Bs' = true <->
              Forall2 (fun a B => wt (As :: G) a B = true) l Bs').
    { induction l as [|a l IHl]; intros [|B Bs']; unfold go in *; cbn.
      - split; auto.
      - split; [discriminate|intro H; inversion H].
      - split; [discriminate|intro H; inversion H].
      - rewrite andb_true_iff, IHl. split.
        + intros [H1 H2]. now constructor.
        + intro H. now inversion H. }
    rewrite Hgo. split.
    + intros [-> H]. split; auto. eauto.
    + intros [-> [Bs' [H1 H2]]]. inversion H1. subst. auto.
  - split; [intros [_ H]; discriminate|intros [_ [Bs [H _]]]; discriminate].
Qed.

Lemma Forall2_update_nth : forall {A B} (R : A -> B -> Prop) f i l l',
  Forall2 R l l' ->
  (forall a b, nth_error l i = Some a -> nth_error l' i = Some b -> R a b -> R (f a) b) ->
  Forall2 R (update_nth i f l) l'.
Proof.
  intros A B R f i l l' H. revert i.
  induction H as [|a b l l' Hab H IH]; intros [|i] Hf; simpl; constructor; auto.
Qed.

(** Replacing the subterm at a head node by a constant of base type
    preserves typing. *)
Lemma wt_repl : forall p G t A c, ctyp c = base ->
  wt G t A = true -> wt G (repl t p (HCst c) []) A = true.
Proof.
  intro p. induction p as [p IH] using (well_founded_induction
    (Wf_nat.well_founded_ltof _ (@length nat))).
  intros G [As h args] A c Hc Ht.
  destruct p as [|[|[|x]] p]; cbn [repl]; auto.
  destruct p as [|[|i] p]; cbn [repl]; auto.
  - apply wt_Lam in Ht. destruct Ht as [-> _].
    apply wt_Lam. split; auto. exists []. simpl. rewrite Hc. split; auto.
  - apply wt_Lam in Ht. destruct Ht as [-> [Bs [Hh Hargs]]].
    apply wt_Lam. split; auto. exists Bs. split; auto.
    apply Forall2_update_nth; auto.
    intros a b _ _ Hab. apply IH; auto. unfold Wf_nat.ltof. simpl. lia.
Qed.

(** ** The transformation T1  [S, Def. 38, Fact 30] *)

Definition T1_applicable (E : ieq) (t : lnf) (n : node) : Prop :=
  in_t n /\ (var_node E t n \/ pos_cst_node E t n) /\
  forall pi j, play E t pi -> j < length pi -> nd E pi j <> n.

Definition T1 (E : ieq) (t : lnf) (n : node) : lnf :=
  replace t n (Lam [] (HCst (cb E)) []).

Theorem T1_sound : forall E t n, WF E t -> T1_applicable E t n ->
  solves E t -> solves E (T1 E t n).
Proof.
  intros E t n HWF [[p ->] [_ Hnv]] Hsol.
  assert (HWF' : WF E (T1 E t (1 :: p))).
  { destruct HWF as [Hwf Hc]. split; auto.
    unfold cand, T1, replace. apply wt_repl; auto. }
  apply (G1_characterisation E _ HWF').
  apply (G1_characterisation E _ HWF) in Hsol.
  assert (Hplays : forall pi, play E (T1 E t (1 :: p)) pi <-> play E t pi).
  { apply locality; auto.
    intros pi j Hpl Hj. symmetry. apply label_at_replace.
    intro Hab. destruct (ancestors_visited E t pi j (1 :: p) HWF Hpl Hj Hab)
      as [i [Hij Hi]].
    exact (Hnv pi i Hpl ltac:(lia) Hi). }
  intros pi Hpl. apply Hsol. now apply Hplays.
Qed.
