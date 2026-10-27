(** * Confluence of beta-reduction on raw terms

    Takahashi's proof: parallel reduction, complete development, the
    triangle property, and the strip lemma.  Used to prove the
    soundness of unfolding without game axioms. *)

From Coq Require Import List Arith Bool Lia Relations.
From HOM Require Import Syntax Lambda.
Import ListNotations.

(** ** Shifting and substitution *)

Ltac leb_cases :=
  repeat match goal with
  | |- context [?a <=? ?b] => destruct (a <=? b) eqn:?
  | |- context [?a =? ?b] => destruct (a =? b) eqn:?
  | |- context [?a <? ?b] => destruct (a <? b) eqn:?
  end;
  repeat match goal with
  | H : (_ <=? _) = true |- _ => apply Nat.leb_le in H
  | H : (_ <=? _) = false |- _ => apply Nat.leb_gt in H
  | H : (_ =? _) = true |- _ => apply Nat.eqb_eq in H
  | H : (_ =? _) = false |- _ => apply Nat.eqb_neq in H
  | H : (_ <? _) = true |- _ => apply Nat.ltb_lt in H
  | H : (_ <? _) = false |- _ => apply Nat.ltb_ge in H
  end.


Lemma shift_0 : forall t c, shift 0 c t = t.
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros c; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - destruct (c <=? n); f_equal; lia.
  - apply IHt.
Qed.

Lemma shift_shift_comm : forall t d d' c c', c' <= c ->
  shift d (c + d') (shift d' c' t) = shift d' c' (shift d c t).
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d d' c c' Hc; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - leb_cases; cbn [shift subst]; leb_cases; f_equal; lia.
  - replace (S (c + d')) with (S c + d') by lia. apply IHt. lia.
Qed.

Lemma shift_shift_in : forall t d d' c c', c <= c' <= c + d ->
  shift d' c' (shift d c t) = shift (d' + d) c t.
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d d' c c' Hc; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - leb_cases; cbn [shift subst]; leb_cases; f_equal; lia.
  - apply IHt. lia.
Qed.

Lemma subst_shift_cancel : forall t d c k u, c <= k <= c + d ->
  subst k u (shift (S d) c t) = shift d c t.
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d c k u Hk; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - leb_cases; cbn [shift subst]; leb_cases; f_equal; lia.
  - apply IHt. lia.
Qed.

Lemma shift_subst_le : forall t d c k u, c <= k ->
  shift d c (subst k u t) = subst (k + d) u (shift d c t).
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d c k u Hk; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - leb_cases; cbn [shift subst]; leb_cases; subst; try (f_equal; lia); try lia.
    rewrite shift_shift_in by lia. f_equal; lia.
  - apply IHt. lia.
Qed.

Lemma shift_subst_ge : forall t d c k u, k <= c ->
  shift d c (subst k u t) = subst k (shift d (c - k) u) (shift d (S c) t).
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros d c k u Hk; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - leb_cases; cbn [shift subst]; leb_cases; subst; try (f_equal; lia); try lia.
    match goal with |- shift _ _ (shift ?k 0 _) = _ =>
      replace c with ((c - k) + k) at 1 by lia end.
    apply shift_shift_comm. lia.
  - replace (c - k) with (S c - S k) by lia. apply IHt. lia.
Qed.

Lemma subst_subst : forall t j k u v, k <= j ->
  subst j u (subst k v t) = subst k (subst (j - k) u v) (subst (S j) u t).
Proof.
  induction t as [n|x|a IHa b IHb|A a IHt]; intros j k u v Hk; cbn [shift subst];
    [ | reflexivity | f_equal; [apply IHa|apply IHb]; try lia | f_equal ].
  - leb_cases; cbn [shift subst]; leb_cases; subst; try (f_equal; lia); try lia.
    + match goal with |- subst _ _ (shift ?k 0 _) = _ =>
        replace j with ((j - k) + k) at 1 by lia end.
      rewrite <- shift_subst_le by lia. reflexivity.
    + rewrite subst_shift_cancel by lia. reflexivity.
  - replace (j - k) with (S j - S k) by lia. apply IHt. lia.
Qed.

(** ** Parallel reduction *)

Inductive par : tm -> tm -> Prop :=
  | par_var n : par (tvar n) (tvar n)
  | par_cst c : par (tcst c) (tcst c)
  | par_app s s' t t' : par s s' -> par t t' -> par (tapp s t) (tapp s' t')
  | par_lam A s s' : par s s' -> par (tlam A s) (tlam A s')
  | par_beta A s s' t t' : par s s' -> par t t' ->
      par (tapp (tlam A s) t) (subst 0 t' s').

Lemma par_refl : forall t, par t t.
Proof. induction t; constructor; auto. Qed.

Lemma beta_par : forall s t, beta s t -> par s t.
Proof. induction 1; constructor; auto using par_refl. Qed.

Lemma red_app : forall s s' t t', red s s' -> red t t' -> red (tapp s t) (tapp s' t').
Proof.
  intros s s' t t' Hs Ht. apply rt_trans with (tapp s' t).
  - induction Hs; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eauto].
  - induction Ht; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma red_lam : forall A s s', red s s' -> red (tlam A s) (tlam A s').
Proof.
  intros A s s' H.
  induction H; [apply rt_step; now constructor|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma par_red : forall s t, par s t -> red s t.
Proof.
  induction 1.
  - apply rt_refl.
  - apply rt_refl.
  - now apply red_app.
  - now apply red_lam.
  - apply rt_trans with (tapp (tlam A s') t').
    + apply red_app; auto. now apply red_lam.
    + apply rt_step. constructor.
Qed.

Lemma par_shift : forall s s', par s s' -> forall d c, par (shift d c s) (shift d c s').
Proof.
  induction 1; intros d k; cbn [shift]; try constructor; auto.
  - destruct (k <=? n); constructor.
  - rewrite shift_subst_ge by lia. rewrite Nat.sub_0_r.
    constructor; auto.
Qed.

Lemma par_subst : forall s s', par s s' -> forall u u' k, par u u' ->
  par (subst k u s) (subst k u' s').
Proof.
  induction 1; intros u u' k Hu; simpl; try constructor; auto.
  - destruct (n =? k); [now apply par_shift|].
    destruct (k <? n); constructor.
  - rewrite subst_subst by lia. rewrite Nat.sub_0_r.
    constructor; auto.
Qed.

(** ** Complete development *)

Fixpoint cd (t : tm) : tm :=
  match t with
  | tapp (tlam A s) u => subst 0 (cd u) (cd s)
  | tapp s u => tapp (cd s) (cd u)
  | tlam A s => tlam A (cd s)
  | _ => t
  end.

Lemma par_cd : forall s t, par s t -> par t (cd s).
Proof.
  induction 1; simpl; try constructor; auto.
  - destruct s; try (constructor; auto).
    inversion H; subst. inversion IHpar1; subst.
    constructor; auto.
  - apply par_subst; auto.
Qed.

Lemma par_diamond : forall t a b, par t a -> par t b ->
  exists d, par a d /\ par b d.
Proof. intros t a b Ha Hb. exists (cd t). split; now apply par_cd. Qed.

(** ** Confluence of [red] *)

Definition pars := clos_refl_trans tm par.

Lemma red_pars : forall s t, red s t -> pars s t.
Proof.
  induction 1; [apply rt_step; now apply beta_par|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma pars_red : forall s t, pars s t -> red s t.
Proof.
  induction 1; [now apply par_red|apply rt_refl|eapply rt_trans; eauto].
Qed.

Lemma strip : forall t a b, par t a -> pars t b ->
  exists d, pars a d /\ par b d.
Proof.
  intros t a b Ha Hb. revert a Ha.
  apply clos_rt_rt1n in Hb. induction Hb as [t|t x b Hx Hb IH]; intros a Ha.
  - exists a. split; [apply rt_refl|auto].
  - destruct (par_diamond t a x Ha Hx) as [d [Had Hxd]].
    destruct (IH d Hxd) as [e [Hde Hbe]].
    exists e. split; auto. eapply rt_trans; [apply rt_step; eauto|auto].
Qed.

Lemma pars_confluent : forall t a b, pars t a -> pars t b ->
  exists d, pars a d /\ pars b d.
Proof.
  intros t a b Ha. revert b.
  apply clos_rt_rt1n in Ha. induction Ha as [t|t x a Hx Ha IH]; intros b Hb.
  - exists b. split; auto. apply rt_refl.
  - destruct (strip t x b Hx Hb) as [d [Hxd Hbd]].
    destruct (IH d Hxd) as [e [Hae Hde]].
    exists e. split; auto. eapply rt_trans; [apply rt_step; eauto|auto].
Qed.

Theorem confluence : forall t a b, red t a -> red t b ->
  exists d, red a d /\ red b d.
Proof.
  intros t a b Ha Hb.
  destruct (pars_confluent t a b (red_pars _ _ Ha) (red_pars _ _ Hb)) as [d [H1 H2]].
  exists d. split; now apply pars_red.
Qed.

(** ** Normal forms *)

Definition normal (t : tm) : Prop := forall t', ~ beta t t'.

Lemma red_normal : forall t t', normal t -> red t t' -> t' = t.
Proof.
  intros t t' Hn H. apply clos_rt_rt1n in H.
  destruct H as [|y z Hy Hz]; [reflexivity|].
  exfalso. exact (Hn y Hy).
Qed.

(** If [t] reduces to a normal form [u] and to [t'], then [t'] reduces
    to [u]. *)
Lemma red_to_normal : forall t t' u, normal u -> red t u -> red t t' -> red t' u.
Proof.
  intros t t' u Hn Hu Ht.
  destruct (confluence t u t' Hu Ht) as [d [Hud Ht'd]].
  apply red_normal in Hud; auto. now subst.
Qed.

Lemma apps_cst_lam : forall l c A s, apps (tcst c) l <> tlam A s.
Proof.
  intros l c A s. unfold apps. destruct l as [|a l] using rev_ind.
  - discriminate.
  - rewrite fold_left_app. discriminate.
Qed.

Lemma normal_apps_cst : forall l c, Forall normal l -> normal (apps (tcst c) l).
Proof.
  intros l. unfold apps. induction l as [|a l IH] using rev_ind; intros c Hl.
  - intros t' H. inversion H.
  - rewrite fold_left_app. simpl. apply Forall_app in Hl as [Hl Ha].
    assert (Hna : normal a) by (now inversion Ha).
    intros t' H. inversion H; subst.
    + exfalso. now apply (apps_cst_lam l c A s).
    + now apply (IH c Hl s').
    + now apply (Hna t'0).
Qed.

Lemma normal_fo2tm : forall r, normal (fo2tm r).
Proof.
  fix IH 1. intros [f l]. simpl. apply normal_apps_cst.
  induction l as [|a l IHl]; simpl; constructor; auto.
Qed.
