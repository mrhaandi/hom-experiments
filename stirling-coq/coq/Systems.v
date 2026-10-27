(** * Systems of interpolation equations

    A system is a finite family of interpolation equations
    [x w̄_1 = u_1, ..., x w̄_m = u_m] with one unknown [x : A]; a solution
    is a single closed lnf [t] that solves every equation (as in
    Padovani's families of equations).  The game is played separately
    for each equation, so the axioms of [Game.v] and [Uniformity.v] apply
    to each member; here we lift the characterisation, T1 and the
    decidability argument to systems. *)

From Coq Require Import List Arith Bool Lia.
From HOM Require Import Syntax Lambda ITree Game GameLemmas Transform Small.
Import ListNotations.

Record isys : Type := ISys {
  sys_args : list ty;               (* A = (A1, ..., Ak, 0) *)
  sys_eqs  : list (list lnf * fo)   (* the pairs (w̄_j, u_j) *)
}.

Definition sys_ty (Sy : isys) : ty := Ty (sys_args Sy).

Definition sys_eq (Sy : isys) (e : list lnf * fo) : ieq :=
  IEq (sys_args Sy) (fst e) (snd e).

Definition eqs (Sy : isys) : list ieq := map (sys_eq Sy) (sys_eqs Sy).

Definition wf_sys (Sy : isys) : Prop := Forall wf_eq (eqs Sy).

Definition cand_sys (Sy : isys) (t : lnf) : Prop := wt [] t (sys_ty Sy) = true.

Definition solves_sys (Sy : isys) (t : lnf) : Prop :=
  cand_sys Sy t /\ Forall (fun E => solves E t) (eqs Sy).

(** Constants: those of all goals plus one fresh [b : 0]. *)
Definition goals (Sy : isys) : list fo := map snd (sys_eqs Sy).

Definition cb_sys (Sy : isys) : cst :=
  Cst (S (list_max (flat_map fo_names (goals Sy)))) base.

Definition C_sys (Sy : isys) : list cst := cb_sys Sy :: flat_map fo_consts (goals Sy).

Definition solution_sys (Sy : isys) (t : lnf) : Prop :=
  solves_sys Sy t /\ incl (consts t) (C_sys Sy).

Definition solvable_sys (Sy : isys) : Prop := exists t, solution_sys Sy t.

Lemma eqs_ty : forall Sy E, In E (eqs Sy) -> eq_ty E = sys_ty Sy.
Proof.
  intros Sy E H. unfold eqs in H. apply in_map_iff in H.
  destruct H as [e [<- _]]. reflexivity.
Qed.

Lemma cand_eqs : forall Sy E t, In E (eqs Sy) -> cand E t <-> cand_sys Sy t.
Proof. intros Sy E t H. unfold cand, cand_sys. now rewrite (eqs_ty Sy E H). Qed.

(** ** Game characterisation for systems (from G1)
    [t] solves the system iff [∀] loses every game [G(t, E_j)]. *)
Theorem G_characterisation_sys : forall Sy t, wf_sys Sy -> cand_sys Sy t ->
  (solves_sys Sy t <-> forall E, In E (eqs Sy) -> forall_loses E t).
Proof.
  intros Sy t Hwf Hc. unfold solves_sys, wf_sys in *. split.
  - intros [_ Hall] E HE. rewrite Forall_forall in Hall, Hwf.
    apply (G1_characterisation E t); [split; [auto|now apply (cand_eqs Sy)]|auto].
  - intros H. split; auto. apply Forall_forall. intros E HE.
    rewrite Forall_forall in Hwf.
    apply (G1_characterisation E t); [split; [auto|now apply (cand_eqs Sy)]|auto].
Qed.

(** ** T1 for systems
    A node may be replaced by [b] if no play of any of the games visits
    it. *)
Definition T1_sys_applicable (Sy : isys) (t : lnf) (n : node) : Prop :=
  forall E, In E (eqs Sy) -> T1_applicable E t n.

Theorem T1_sys_sound : forall Sy t n, wf_sys Sy -> in_t n ->
  T1_sys_applicable Sy t n -> solves_sys Sy t -> solves_sys Sy (T1c t n (cb_sys Sy)).
Proof.
  intros Sy t n Hwf [p ->] Happ [Hc Hall]. unfold wf_sys in Hwf. split.
  - unfold cand_sys, T1c, replace. apply wt_repl; auto.
  - apply Forall_forall. intros E HE. rewrite Forall_forall in Hall, Hwf.
    apply T1c_sound; auto.
    split; [auto|now apply (cand_eqs Sy)].
Qed.

(** ** Small solutions and decidability for systems *)

Definition q_sys (Sy : isys) : nat :=
  Nat.max (ar (sys_ty Sy)) (list_max (flat_map fo_arities (goals Sy))).

Definition p_sys (Sy : isys) : nat := ord (sys_ty Sy) / 2.

(** The analogue of the bound of [S, Thm. 37]: |u| is replaced by the
    total size of the goals, since the plays of all games share [t]. *)
Definition bound_sys (Sy : isys) : nat :=
  let p := p_sys Sy in let q := q_sys Sy in
  4 * (p * p) * q ^ (2 * p - 2) * list_sum (map fo_size (goals Sy)).

Definition Thm37_sys : Prop :=
  forall Sy, wf_sys Sy -> solvable_sys Sy ->
    exists t, solution_sys Sy t /\ depth t <= bound_sys Sy.

Lemma solves_sys_dec : forall Sy t, {solves_sys Sy t} + {~ solves_sys Sy t}.
Proof.
  intros Sy t. unfold solves_sys, cand_sys.
  destruct (wt [] t (sys_ty Sy)) eqn:Hw.
  - destruct (Forall_dec (fun E => solves E t) (fun E => L1_solves_dec E t) (eqs Sy))
      as [H|H]; [left|right]; tauto.
  - right. intros [H _]. discriminate.
Defined.

Lemma solution_sys_dec : forall Sy t, {solution_sys Sy t} + {~ solution_sys Sy t}.
Proof.
  intros Sy t. unfold solution_sys.
  assert (Hd : forall c d : cst, {c = d} + {c <> d}).
  { intros c d. destruct (cst_eqb c d) eqn:H.
    - left. now apply cst_eqb_eq.
    - right. intro e. apply cst_eqb_eq in e. congruence. }
  destruct (solves_sys_dec Sy t) as [H1|H1];
    [|right; tauto].
  assert (H2 : {incl (consts t) (C_sys Sy)} + {~ incl (consts t) (C_sys Sy)}).
  { induction (consts t) as [|c l IH].
    - left. intros c [].
    - destruct (in_dec Hd c (C_sys Sy)) as [Hc|Hc].
      + destruct IH as [IH|IH].
        * left. intros d [<-|Hd']; auto.
        * right. intro H. apply IH. intros d Hd'. apply H. now right.
      + right. intro H. apply Hc, H. now left. }
  destruct H2; [left|right]; tauto.
Defined.

Theorem decidable_systems : Thm37_sys ->
  forall Sy, wf_sys Sy -> {solvable_sys Sy} + {~ solvable_sys Sy}.
Proof.
  intros H37 Sy Hwf.
  destruct (Exists_dec (solution_sys Sy) (enum (bound_sys Sy) [] (C_sys Sy) (sys_ty Sy))
              (solution_sys_dec Sy)) as [Hex|Hnex].
  - left. apply Exists_exists in Hex. destruct Hex as [t [_ Ht]]. now exists t.
  - right. intros Hs. destruct (H37 Sy Hwf Hs) as [t [Ht Hd]].
    apply Hnex. apply Exists_exists. exists t. split; auto.
    destruct Ht as [[Hc _] Hce].
    apply enum_complete; auto.
Qed.

(** ** A single equation is a system with one member *)

Definition single (E : ieq) : isys := ISys (eq_args E) [(eq_ws E, eq_goal E)].

Lemma single_eqs : forall E, eqs (single E) = [E].
Proof. intros [As ws u]. reflexivity. Qed.

Lemma single_C : forall E, C_sys (single E) = CE E.
Proof.
  intros [As ws u]. unfold C_sys, CE, cb_sys, cb, goals. simpl.
  now rewrite !app_nil_r.
Qed.

Lemma single_solution : forall E t, solution_sys (single E) t <-> solution E t.
Proof.
  intros E t. unfold solution_sys, solution, solves_sys, in_CE.
  rewrite single_eqs, single_C. split.
  - intros [[_ H] Hc]. inversion H. split; auto.
  - intros [Hs Hc]. split; auto. split.
    + destruct Hs as [Hc' _]. exact Hc'.
    + constructor; auto.
Qed.

Lemma single_bound : forall E, bound_sys (single E) = bound E.
Proof.
  intros [As ws u]. unfold bound_sys, bound, p_sys, p_of, q_sys, q_of, goals.
  cbn [single sys_eqs sys_args eq_args eq_goal map flat_map list_sum].
  rewrite app_nil_r. cbn [snd]. unfold list_sum. cbn [fold_right].
  rewrite Nat.add_0_r. reflexivity.
Qed.

(** The theorem for systems contains the theorem for one equation. *)
Theorem Thm37_sys_single : Thm37_sys -> Thm37.
Proof.
  intros H E Hwf [t Ht].
  assert (Hw : wf_sys (single E)).
  { unfold wf_sys. rewrite single_eqs. now constructor. }
  destruct (H (single E) Hw) as [t' [Ht' Hd]].
  - exists t. now apply single_solution.
  - exists t'. split; [now apply single_solution|now rewrite <- single_bound].
Qed.
