import unittest

from typer import siam
from typer.derive import Deriv
from typer.itypes import Arrow, Inter
from typer.parser import TyperError, parse_term
from typer.reduce import WEAK_HEAD, normalize
from typer.siam import STAR
from typer.terms import Var

T = parse_term
I = "(fun z. z)"
TERMS = {
    "paper": f"(fun y x. x y) {I} {I}",
    "identity": f"{I} {I}",
    "duplication": f"(fun x. x x) {I} {I}",
    "church": f"(fun f x. f (f x)) (fun f x. f (f x)) {I} {I}",
    "erasing": f"(fun x y. y) ({I} {I}) {I}",
    "nested": f"(fun x. x {I}) (fun y. y) ",
}


def run_of(term: str) -> siam.Run:
    d, _ = siam.weak_head_derivation(T(term))
    return siam.run(d)


class SequenceDerivations(unittest.TestCase):
    def test_weak_head_derivation_is_a_sequence_derivation(self):
        for name, term in TERMS.items():
            with self.subTest(term=name):
                d, steps = siam.weak_head_derivation(T(term))
                siam.check_sequence(d)
                self.assertEqual(d.type, STAR)
                self.assertEqual(d.term, T(term))
                self.assertEqual(steps, normalize(T(term), WEAK_HEAD).steps)

    def test_sequences_keep_multiplicity_and_order(self):
        d, _ = siam.weak_head_derivation(T(TERMS["duplication"]))
        inner = d.premises[0].premises[0]  # the abstraction fun x. x x
        self.assertEqual(len(siam.seq(inner.type.dom)), 2)

    def test_checker_rejects_a_wrong_order(self):
        d, _ = siam.weak_head_derivation(T(f"(fun x. x {I}) (fun y. fun w. y)"))
        bad = Deriv(d.rule, d.term, d.type, (d.premises[0], *reversed(d.premises[1:])))
        if len(d.premises) > 2:
            with self.assertRaises(TyperError):
                siam.check_sequence(bad)

    def test_checker_rejects_a_bad_lamstar(self):
        d = Deriv("lamstar", T("fun x. x"), Arrow(Inter(()), STAR))
        with self.assertRaises(TyperError):
            siam.check_sequence(d)

    def test_open_terms_are_refused(self):
        with self.assertRaises(TyperError):
            siam.weak_head_derivation(T("fun x. q x"))


class Runs(unittest.TestCase):
    def test_every_star_visited_exactly_once(self):
        for name, term in TERMS.items():
            with self.subTest(term=name):
                r = run_of(term)
                self.assertTrue(r.each_star_once())
                self.assertEqual(len(r.states), len(r.stars()))

    def test_starts_and_ends_as_in_the_paper(self):
        r = run_of(TERMS["paper"])
        self.assertEqual(r.states[0], siam.State(0, (), siam.UP))
        self.assertEqual(r.index.nodes[r.states[-1].node].rule, "lamstar")
        self.assertEqual(len(r.states), 19)

    def test_the_paper_example_annotations(self):
        r = run_of(TERMS["paper"])
        lines = siam.show_run(r).splitlines()
        self.assertEqual(lines[0], "(T-@) |- (fun y x. x y) (fun z. z) (fun z. z) : ★↑1")
        self.assertIn("(T-λ) |- fun y x. x y : [★↓18] -> [[★↑14] -> ★↓8] -> ★↑3", lines[2])
        self.assertIn("(T-Var) x : [[★] -> ★] |- x : [★↓16] -> ★↑6", lines[5])
        self.assertIn("(T-λ★) |- fun z. z : ★↑19", lines[7])
        self.assertIn("(T-λ) |- fun z. z : [★↓12] -> ★↑10", lines[8])

    def test_is_bideterministic(self):
        """Every state has one successor, and no two states share one."""
        for name, term in TERMS.items():
            with self.subTest(term=name):
                r = run_of(term)
                self.assertEqual(len(set(r.states)), len(r.states))

    def test_any_type_needs_the_flag(self):
        d = Deriv("lamstar", T("fun x. x"), STAR)
        arrow = Deriv("abs", T("fun x. x"), Arrow(Inter((STAR,)), STAR), (Deriv("var", Var("x"), STAR),))
        self.assertEqual(len(siam.run(d).states), 1)
        with self.assertRaises(TyperError):
            siam.run(arrow)
        r = siam.run(arrow, any_type=True)
        self.assertTrue(r.each_star_once())


if __name__ == "__main__":
    unittest.main()
