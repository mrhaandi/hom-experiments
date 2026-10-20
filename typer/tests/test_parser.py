import unittest

from typer.itypes import OMEGA, Arrow, Atom, Inter
from typer.parser import Canonical, TyperError, parse_program, parse_term, parse_type
from typer.terms import NF, App, Lam, Var, alpha_eq, subst

a, b, c = Atom("a"), Atom("b"), Atom("c")
x, y, z = Var("x"), Var("y"), Var("z")


class TypeSyntax(unittest.TestCase):
    def test_arrow_is_right_associative(self):
        self.assertEqual(parse_type("a -> b -> c"), Arrow(a, Arrow(b, c)))

    def test_intersection_binds_tighter_than_arrow(self):
        self.assertEqual(parse_type("a /\\ b -> c"), Arrow(Inter((a, b)), c))

    def test_example_declaration(self):
        self.assertEqual(parse_type("a /\\ (a -> a)"), Inter((a, Arrow(a, a))))

    def test_repeated_components_are_kept(self):
        self.assertEqual(parse_type("a /\\ a"), Inter((a, a)))

    def test_nested_intersection_is_flattened(self):
        self.assertEqual(parse_type("a /\\ (b /\\ c)"), Inter((a, b, c)))

    def test_omega_and_unicode(self):
        self.assertEqual(parse_type("omega -> a"), Arrow(OMEGA, a))
        self.assertEqual(parse_type("ω → a ∧ b"), Arrow(OMEGA, Inter((a, b))))

    def test_round_trip(self):
        for s in ["a -> b -> c", "(a -> b) -> c", "a /\\ (a -> a) -> a", "omega -> a"]:
            self.assertEqual(str(parse_type(s)), s)


class TermSyntax(unittest.TestCase):
    def test_application_is_left_associative(self):
        self.assertEqual(parse_term("x y z"), App(App(x, y), z))

    def test_lambda_extends_right(self):
        self.assertEqual(parse_term("fun x.x y"), Lam("x", App(x, y)))

    def test_multi_binder_abbreviation(self):
        self.assertEqual(parse_term("fun x y. x y"), parse_term("fun x.fun y.x y"))

    def test_lambda_as_last_argument(self):
        self.assertEqual(parse_term("x fun y. y"), App(x, Lam("y", y)))

    def test_alternative_lambda_symbols(self):
        self.assertEqual(parse_term("\\x. x"), parse_term("λx. x"))
        self.assertEqual(parse_term("\\x. x"), parse_term("fun x. x"))

    def test_nf(self):
        self.assertEqual(parse_term("NF((fun x.x) y)"), NF(App(Lam("x", x), y)))

    def test_errors_have_positions(self):
        with self.assertRaises(TyperError) as cm:
            parse_term("fun x x")
        self.assertEqual(cm.exception.col, 8)


class Substitution(unittest.TestCase):
    def test_capture_is_avoided(self):
        t = subst(Lam("y", App(x, y)), "x", y)
        self.assertTrue(alpha_eq(t, parse_term("fun z. y z")))

    def test_alpha_eq_distinguishes_free_from_bound(self):
        self.assertFalse(alpha_eq(parse_term("fun x. y"), parse_term("fun y. y")))
        self.assertTrue(alpha_eq(parse_term("fun x. x"), parse_term("fun y. y")))


class Programs(unittest.TestCase):
    EXAMPLE = """\
v : a /\\ (a -> a)

M = fun x.fun y.x y
N = fun x y. a x y
N1 = v v
M1 = (fun x.x)(fun y.y)
M2 = NF(M1)
cannonical: M2
"""

    def test_example_file(self):
        p = parse_program(self.EXAMPLE)
        self.assertEqual(p.env, {"v": Inter((a, Arrow(a, a)))})
        self.assertEqual(list(p.defs), ["M", "N", "N1", "M1", "M2"])
        self.assertEqual(p.defs["N"], parse_term("fun x y. a x y"))
        self.assertEqual(p.defs["M2"], NF(parse_term("(fun x.x)(fun y.y)")))
        self.assertEqual(p.commands, [Canonical(p.defs["M2"], "M2", 8)])

    def test_comments_and_blank_lines(self):
        p = parse_program("# comment\n\nI = fun x. x  # identity\n")
        self.assertEqual(p.defs["I"], Lam("x", x))

    def test_defined_names_are_substituted_without_capture(self):
        p = parse_program("K = fun x y. x\nP = fun y. K y\n")
        self.assertTrue(alpha_eq(p.defs["P"], parse_term("fun y. (fun x y'. x) y")))
        p = parse_program("N = a\nQ = fun a. N a\n")
        self.assertTrue(alpha_eq(p.defs["Q"], parse_term("fun b. a b")))

    def test_bound_variable_shadows_definition_name(self):
        p = parse_program("I = fun x. x\nJ = fun I. I\n")
        self.assertTrue(alpha_eq(p.defs["J"], parse_term("fun z. z")))

    def test_self_reference_is_an_error(self):
        with self.assertRaises(TyperError) as cm:
            parse_program("M1 = x\nM2 = NF(M2)\n")
        self.assertEqual(cm.exception.line, 2)
        self.assertIn("used before it is defined", cm.exception.msg)

    def test_redefinition_is_an_error(self):
        with self.assertRaises(TyperError):
            parse_program("I = fun x. x\nI = fun y. y\n")

    def test_type_of_defined_name_is_an_error(self):
        with self.assertRaises(TyperError):
            parse_program("I : a\nI = fun x. x\n")

    def test_missing_operator_is_an_error(self):
        with self.assertRaises(TyperError) as cm:
            parse_program("I fun x. x\n")
        self.assertIn("expected ':' or '='", cm.exception.msg)


if __name__ == "__main__":
    unittest.main()


class MultiLine(unittest.TestCase):
    def test_indented_continuation_lines(self):
        p = parse_program("a : o\nb : o\n\nM = fun x y.\n    x (fun z.\n      z y)\n      a\n\nN = M b\n")
        self.assertEqual(p.defs["M"], parse_term("fun x y. x (fun z. z y) a"))
        self.assertEqual(list(p.env), ["a", "b"])

    def test_blank_line_ends_a_statement(self):
        p = parse_program("M = fun x.\nx\n\nN = M\n")
        self.assertEqual(p.defs["M"], parse_term("fun x. x"))

    def test_unindented_new_statement_ends_the_previous_one(self):
        p = parse_program("M = fun x.\n  x\nN = M\nv : o ->\n  o\n")
        self.assertEqual(p.defs["N"], parse_term("fun x. x"))
        self.assertEqual(str(p.env["v"]), "o -> o")

    def test_comments_inside_a_statement(self):
        p = parse_program("M = fun x.   # the identity\n  x\n")
        self.assertEqual(p.defs["M"], parse_term("fun x. x"))

    def test_errors_report_the_right_line_and_column(self):
        with self.assertRaises(TyperError) as cm:
            parse_program("a : o\n\nM = fun x.\n    x (fun z.\n      z ) )\n")
        self.assertEqual((cm.exception.line, cm.exception.col), (5, 11))
        with self.assertRaises(TyperError) as cm:
            parse_program("M = fun x.\n")
        self.assertEqual(cm.exception.line, 1)
