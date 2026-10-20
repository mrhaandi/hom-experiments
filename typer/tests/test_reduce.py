import unittest

from typer.parser import TyperError, parse_term
from typer.reduce import find_redex, is_normal, normalize
from typer.terms import alpha_eq, show_term

T = parse_term
I = "(fun x. x)"
K = "(fun x y. x)"
D = "(fun x. x x)"
O = f"({D} {D})"
TWO = "(fun f x. f (f x))"


class Normality(unittest.TestCase):
    def test_normal_forms(self):
        for s in ["x", "fun x. x", "x (fun y. y)", "fun x. x (x y)"]:
            self.assertTrue(is_normal(T(s)), s)

    def test_redex_under_lambda_is_not_normal(self):
        self.assertFalse(is_normal(T(f"fun y. {I} y")))


class Strategies(unittest.TestCase):
    def test_cbn_picks_outermost(self):
        self.assertEqual(find_redex(T(f"{K} {I} ({I} z)"), "cbn"), ("f",))

    def test_cbv_picks_innermost(self):
        self.assertEqual(find_redex(T(f"{K} {I} ({I} z)"), "cbv"), ("f",))
        self.assertEqual(find_redex(T(f"{K} y ({I} z)"), "cbv"), ("f",))
        self.assertEqual(find_redex(T(f"(fun x. y) ({I} z)"), "cbv"), ("a",))

    def test_both_reduce_under_lambda(self):
        for s in ("cbn", "cbv"):
            self.assertEqual(find_redex(T(f"fun y. {I} y"), s), ("b",))

    def test_same_normal_form(self):
        t = T(f"{TWO} {TWO} {I}")
        n, v = normalize(t, "cbn"), normalize(t, "cbv")
        self.assertTrue(alpha_eq(n.result, T("fun x. x")))
        self.assertTrue(alpha_eq(v.result, T("fun x. x")))

    def test_cbv_diverges_where_cbn_terminates(self):
        t = T(f"{K} {I} {O}")
        self.assertEqual(normalize(t, "cbn").steps, 2)
        with self.assertRaises(TyperError):
            normalize(t, "cbv", max_steps=100)

    def test_cbv_duplicates_less(self):
        t = T(f"{D} ({I} {I})")
        self.assertEqual(normalize(t, "cbn").steps, 4)
        self.assertEqual(normalize(t, "cbv").steps, 3)

    def test_trace_records_every_step(self):
        tr = normalize(T(f"{I} ({I} z)"), "cbn")
        self.assertEqual([show_term(t) for t in tr.terms], ["(fun x. x) ((fun x. x) z)", "(fun x. x) z", "z"])
        self.assertEqual(tr.redexes, ((), ()))
        tr = normalize(T(f"{I} ({I} z)"), "cbv")
        self.assertEqual(tr.redexes, (("a",), ()))


class Printing(unittest.TestCase):
    def test_mark_redex(self):
        t = T(f"fun y. {I} ({I} y)")
        self.assertEqual(show_term(t, ("b",)), "fun y. [(fun x. x) ((fun x. x) y)]")
        self.assertEqual(show_term(t, ("b", "a")), "fun y. (fun x. x) [(fun x. x) y]")

    def test_mark_inside_multi_binder(self):
        t = T(f"fun y z. {I} z")
        self.assertEqual(show_term(t, ("b", "b")), "fun y z. [(fun x. x) z]")
        self.assertEqual(show_term(T("fun y z. z"), ("b",)), "fun y. [fun z. z]")


if __name__ == "__main__":
    unittest.main()
