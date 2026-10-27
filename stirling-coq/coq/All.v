(** * Summary: the main results and the assumptions they depend on. *)

From HOM Require Import Syntax Lambda ITree Game GameLemmas Transform
  Uniformity Section6 Small.

(** Fact 30 of the paper (T1 preserves solutions). *)
Print Assumptions T1_sound.
(** Unique partition of plays (Fact 33). *)
Print Assumptions stage_unique.
(** At most depth(u) disjoint contributing intervals. *)
Print Assumptions disjoint_contributions.
(** Ancestors of a visited node are visited earlier. *)
Print Assumptions ancestors_visited.
(** Thm. 37 implies decidability. *)
Print Assumptions decidable_interpolation.
