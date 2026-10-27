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

## Assumptions
- G1–G10, U1–U7: results of the game part, as `Axiom`s.
- `L1_solves_dec`: decidability of `solves`. This is standard (strong normalisation and confluence) but not proved here.
- Thm. 37 is a hypothesis of `decidable_interpolation`, not an axiom.

No `Admitted` anywhere.

## Not formalized
- The enlarged combs and the unfolded term (Def. 47), with their soundness. This is the main gap in the paper.
- The counting in the proof of Thm. 37, Prop. 32, and the soundness of T2.
- The reduction from matching to interpolation (Prop. 5, Fact 6) and Section 6.5.
