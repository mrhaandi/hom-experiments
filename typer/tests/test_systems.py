import unittest

from typer.evaluate import evaluate
from typer.parser import TyperError, parse_program, parse_term, parse_type
from typer.systems import SYSTEMS, SystemTypeError, get_system
from typer.terms import alpha_eq

P = parse_type


class Systems(unittest.TestCase):
    def test_four_systems(self):
        self.assertEqual(set(SYSTEMS), {"idem", "idem-omega", "nonidem", "nonidem-omega"})

    def test_idempotent_intersection_is_a_set(self):
        s = get_system("idem")
        self.assertTrue(s.equal(P("a /\\ a"), P("a")))
        self.assertTrue(s.equal(P("a /\\ b -> c"), P("b /\\ a /\\ b -> c")))

    def test_non_idempotent_intersection_is_a_multiset(self):
        s = get_system("nonidem")
        self.assertFalse(s.equal(P("a /\\ a"), P("a")))
        self.assertTrue(s.equal(P("a /\\ b /\\ a -> c"), P("b /\\ a /\\ a -> c")))

    def test_types_are_strict(self):
        for s in SYSTEMS.values():
            with self.assertRaises(SystemTypeError):
                s.check(P("a -> b /\\ c"))
            s.check(P("a /\\ b -> c"))

    def test_omega_only_in_omega_systems(self):
        for name, s in SYSTEMS.items():
            if s.omega:
                s.check(P("omega -> a"))
            else:
                with self.assertRaises(SystemTypeError):
                    s.check(P("omega -> a"))


class Evaluation(unittest.TestCase):
    SRC = "v : a /\\ (a -> a)\nM1 = (fun x.x)(fun y.y)\nM2 = NF(M1)\ncannonical: M2\n"

    def test_example(self):
        ev = evaluate(parse_program(self.SRC), get_system("idem"))
        self.assertTrue(alpha_eq(ev.defs["M2"], parse_term("fun y. y")))
        self.assertEqual(ev.traces["M2"].steps, 1)
        self.assertEqual(len(ev.canonical), 1)

    def test_canonical_requires_normal_form(self):
        with self.assertRaises(TyperError) as cm:
            evaluate(parse_program("M1 = (fun x.x) y\ncannonical: M1\n"), get_system("idem"))
        self.assertIn("not in normal form", cm.exception.msg)
        self.assertEqual(cm.exception.line, 2)

    def test_declarations_are_checked_against_the_system(self):
        prog = parse_program("v : omega -> a\n")
        evaluate(prog, get_system("idem-omega"))
        with self.assertRaises(TyperError) as cm:
            evaluate(prog, get_system("idem"))
        self.assertEqual(cm.exception.line, 1)

    def test_nested_nf(self):
        ev = evaluate(parse_program("A = NF(fun z. NF((fun x. x) z) z)\n"), get_system("idem"))
        self.assertTrue(alpha_eq(ev.defs["A"], parse_term("fun z. z z")))
        self.assertEqual(ev.traces["A"].steps, 0)

    def test_divergence_reports_the_line(self):
        with self.assertRaises(TyperError) as cm:
            evaluate(parse_program("\nO = NF((fun x. x x)(fun x. x x))\n"), get_system("idem"), max_steps=20)
        self.assertEqual(cm.exception.line, 2)


if __name__ == "__main__":
    unittest.main()
