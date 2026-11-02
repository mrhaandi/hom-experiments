# Coq formalization of Stirling's decidability proof

Source: C. Stirling, *An introduction to decidability of higher-order matching*.
Checked with Coq 8.18 (`make` in this folder; `All.v` prints the assumptions of the main results).

## Files
- `Syntax.v`: types, order and arity, first-order goal terms (restrictions R1, R2 are built in), long normal forms with dummy lambdas, typing.
- `Lambda.v`: de Bruijn λ-terms, β-reduction, embedding of lnf, interpolation equations, `solves`, `C_E`, `solution`, `solvable`.
- `ITree.v`: interpolation trees (nodes as addresses), labels, binding, level, embedded, family, end. Also subtree replacement.
- `Game.v`: states, look-up tables, moves (Fig. 5), runs and plays, parent, chain. **Axioms G1–G10** (Section 4 of the paper).
- `GameLemmas.v`: proved lemmas. States change only at constants. Disjoint contributing intervals number at most depth(u). Runs extend to plays. Ancestors of a visited node are visited earlier.
- `Transform.v`: locality of the game (proved). Typing is preserved by replacement (proved). **T1 preserves solutions, Fact 30 (proved)**.
- `Uniformity.v`: correspondence, complementary intervals, recurrence property. **Axioms U1–U7** (Section 6.1).
- `Section6.v`: end paths, redundancy, T2, stages of a play, combs and paths, partition tree, unfolding conditions. **The partition is unique, Fact 33 (proved)**. The gaps are stated as named propositions (`Gap_T2_sound`, `Gap_partition_tree`, `Gap_coverage`); they are not assumed.
- `Small.v`: the bound 4p²q^(2p−2)|u| and `Thm37` (the statement of Thm. 37) as a proposition. Enumeration of lnf of bounded depth, with completeness proved. **`decidable_interpolation : Thm37 -> {solvable E} + {~ solvable E}` (proved)**.
- `Confluence.v`: confluence of β on raw terms (Takahashi's parallel reduction); `red_to_normal`, `normal_fo2tm`. No axioms.
- `Unfolding.v`: one-step unfolding at a z-node whose `w_i = λx̄. x_j B̄` has a linear head (x_j not free in B̄), on raw terms. **`unfold_sound`: if `t w̄ →β* u` (u normal) then `t' w̄ →β* u`**, proved without axioms. See `../order5-unfolding.md`.
- `Systems.v`: systems of interpolation equations `x w̄_j = u_j` (j = 1..m) sharing one unknown `x : A`; a solution is one `t` solving all of them, with constants from `{b} ∪ consts(u_1..u_m)`. Proved for systems: the game characterisation via G1 (`G_characterisation_sys`), T1 soundness when no play of any of the m games visits the node (`T1_sys_sound`), and **`decidable_systems : Thm37_sys -> {solvable_sys S} + {~ solvable_sys S}`**. `Thm37_sys` is Thm. 37 with |u| replaced by Σ|u_j|; `Thm37_sys_single : Thm37_sys -> Thm37` shows it contains the single-equation statement.

## Assumptions
- G1–G10, U1–U7: results of the game part, as `Axiom`s.
- `L1_solves_dec`: decidability of `solves`. This is standard (strong normalisation and confluence) but not proved here.
- Thm. 37 is a hypothesis of `decidable_interpolation`, not an axiom.

No `Admitted` anywhere.

## Not formalized
- The enlarged combs and the unfolded term (Def. 47), with their soundness. This is the main gap in the paper.
- The counting in the proof of Thm. 37, Prop. 32, and the soundness of T2.
- The reduction from matching to interpolation (Prop. 5, Fact 6) and Section 6.5.
