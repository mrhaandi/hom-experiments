import re
import unittest

from typer import latex
from typer.derive import Deriv, Expander, canonical
from typer.itypes import Atom
from typer.parser import parse_term, parse_type
from typer.reduce import normalize
from typer.systems import get_system
from typer.terms import Var

T = parse_term
INFER = {"AxiomC": 0, "UnaryInfC": 1, "BinaryInfC": 2, "TrinaryInfC": 3, "QuaternaryInfC": 4, "QuinaryInfC": 5}


def balanced(s: str) -> bool:
    depth = 0
    for ch in re.sub(r"\\[{}]", "", s):
        depth += {"{": 1, "}": -1}.get(ch, 0)
        if depth < 0:
            return False
    return depth == 0


def tree_is_complete(tex: str) -> bool:
    """Simulates the bussproofs stack: one tree left at \\DisplayProof."""
    stack = 0
    for cmd in re.findall(r"\\(AxiomC|UnaryInfC|BinaryInfC|TrinaryInfC|QuaternaryInfC|QuinaryInfC)\b", tex):
        n = INFER[cmd]
        if stack < n:
            return False
        stack = stack - n + 1
    return stack == 1


class Notation(unittest.TestCase):
    def test_terms(self):
        self.assertEqual(latex.term_tex(T("fun x y. x (y z)")), r"\lambda x\,y.\,x\,(y\,z)")
        self.assertEqual(latex.term_tex(T("two I")), r"\mathit{two}\,I")
        self.assertEqual(latex.term_tex(T("z ((fun x. x) y)"), ("a",)), r"z\,(\underline{(\lambda x.\,x)\,y})")

    def test_indexed_names(self):
        self.assertEqual(latex.name_tex("M2"), "M_{2}")
        self.assertEqual(latex.name_tex("x1'"), "x_{1}'")
        self.assertEqual(latex.name_tex("two"), r"\mathit{two}")

    def test_source(self):
        from typer.parser import parse_program

        prog = parse_program("v : a /\\ (a -> a)\nM1 = (fun x.x)(fun y.y)\nM2 = NF(M1)\ncannonical: M2\n")
        tex = latex.source_tex(prog.statements, get_system("idem"))
        self.assertIn(r"v &: a \cap (a \to a)", tex)
        self.assertIn(r"M_{1} &= (\lambda x.\,x)\,(\lambda y.\,y)", tex)
        self.assertIn(r"M_{2} &= \mathrm{NF}(M_{1})", tex)
        self.assertIn(r"\textbf{canonical: } M_{2}", tex)
        self.assertTrue(balanced(tex))

    def test_types_per_system(self):
        t = parse_type("a /\\ (a -> b) -> b")
        self.assertEqual(latex.type_tex(t, get_system("idem")), r"(a \cap (a \to b)) \to b")
        self.assertEqual(latex.type_tex(t, get_system("nonidem")), r"[a, [a] \to b] \to b")
        self.assertEqual(latex.type_tex(parse_type("omega -> a"), get_system("idem-omega")), r"\omega \to a")
        self.assertEqual(latex.type_tex(parse_type("omega -> a"), get_system("nonidem-omega")), r"[\,] \to a")
        self.assertEqual(latex.type_tex(parse_type("a -> b"), get_system("nonidem")), r"[a] \to b")

    def test_generated_atoms(self):
        self.assertEqual(latex.atom_tex("a_{ε}"), r"a_{\varepsilon}")
        self.assertEqual(latex.atom_tex("b_{0^2,1}"), "b_{0^2,1}")


class Documents(unittest.TestCase):
    def test_derivations_are_well_formed(self):
        tr = normalize(T("(fun f x y. f y x) (fun a b. a (b b)) ((fun z. z) (fun z. z))"), "cbn")
        for name in ("idem", "nonidem-omega"):
            s = get_system(name)
            for d in Expander(s).along(tr):
                for width in (60, latex.DEFAULT_WIDTH, 1000):
                    for tree in latex.derivation_trees(d, s, width):
                        self.assertTrue(balanced(tree))
                        self.assertTrue(tree_is_complete(tree))

    def test_wide_subtrees_get_labels_in_reading_order(self):
        s = get_system("idem")
        tr = normalize(T("(fun f x y. f y x) (fun a b. a (b b)) ((fun z. z) (fun z. z))"), "cbn")
        d = Expander(s).along(tr)[0]
        self.assertEqual(len(latex.derivation_trees(d, s, 10000)), 1)
        trees = latex.derivation_trees(d, s, 150)
        self.assertGreater(len(trees), 1)
        text = "\n".join(trees)
        for k in range(1, len(trees)):
            self.assertIn(latex.label_tex(k), text)
        first = [int(m) for m in re.findall(r"tree(\d+)", text)]
        self.assertEqual(sorted(set(first)), list(range(1, len(trees))))
        self.assertEqual(first[0], 1)
        tex = latex.derivation_tex(d, s, 150)
        self.assertNotIn("adjustbox", tex)
        self.assertIn(r"\noindent $\textsf{tree1}$:", tex)

    def test_many_premises_are_split_off(self):
        s = get_system("nonidem")
        a = Atom("a")
        args = [Deriv("var", Var("y"), a)] * 6
        fun = Deriv("var", Var("x"), parse_type("a /\\ a /\\ a /\\ a /\\ a /\\ a -> a"))
        d = Deriv("app", T("x y"), a, (fun, *args))
        section = latex.derivation_section("x", d, s)
        self.assertIn(r"\textsf{tree1} \quad \textsf{tree2} \quad \textsf{tree3}", section)
        self.assertIn(r"\QuinaryInfC", section)
        self.assertTrue(balanced(section))
        trees = latex.derivation_trees(d, s)
        self.assertEqual(len(trees), 4)
        self.assertTrue(all(tree_is_complete(t) for t in trees))

    def test_document(self):
        doc = latex.document(latex.derivation_section("x", canonical(T("fun x. x"), get_system("idem")), get_system("idem")))
        self.assertTrue(doc.startswith(r"\documentclass"))
        self.assertTrue(doc.rstrip().endswith(r"\end{document}"))
        self.assertTrue(balanced(doc))


if __name__ == "__main__":
    unittest.main()


class Shortening(unittest.TestCase):
    TERM = "(fun f x y. f y x) (fun a b. a (b b)) ((fun z. z) (fun z. z))"

    def derivation(self, system):
        s = get_system(system)
        return s, Expander(s).along(normalize(T(self.TERM), "cbn"))[0]

    def test_stacked_intersections(self):
        t = parse_type("a /\\ (a -> b) -> b")
        st = latex.PLAIN.with_(stacked=True)
        idem = latex.type_tex(t, get_system("idem"), st)
        self.assertIn(r"\begin{array}[c]{@{}l@{}}a \cap \\ (a \to b)\end{array}", idem)
        nonidem = latex.type_tex(t, get_system("nonidem"), st)
        self.assertIn(r"\left[\begin{array}[c]{@{}l@{}}a, \\ [a] \to b\end{array}\right]", nonidem)
        self.assertLess(latex.tex_width(idem), latex.tex_width(latex.type_tex(t, get_system("idem"))))

    def test_plain_when_everything_fits(self):
        s, d = self.derivation("idem")
        self.assertEqual(latex.plan_style(d, s, 1000), latex.PLAIN)

    def test_short_atoms_then_abbreviations(self):
        s, d = self.derivation("idem")
        st = latex.plan_style(d, s, 150)
        self.assertTrue(st.atoms)
        self.assertEqual(st.abbrevs, ())
        st = latex.plan_style(d, s, 60)
        self.assertTrue(st.abbrevs)
        for x in latex._subderivations(d):
            self.assertLessEqual(latex.tex_width(latex.fitted_judgement(x, s, st, 60)), 60)

    def test_section_has_legend(self):
        s, d = self.derivation("nonidem-omega")
        section = latex.derivation_section("x", d, s, 60)
        self.assertIn(r"\tau_{1} &=", section)
        self.assertIn(r"\alpha_{1} = a_{", section)
        self.assertTrue(balanced(section))
        for tree in latex.derivation_trees(d, s, 60, latex.plan_style(d, s, 60)):
            self.assertTrue(tree_is_complete(tree))


class Ascii(unittest.TestCase):
    """LaTeX without inputenc/unicode setup rejects characters such as ★, λ, ε or ω."""

    def test_documents_are_ascii(self):
        import contextlib
        import io
        import os

        from typer.__main__ import main

        root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
        runs = [
            ["examples/normal_form.txt", "--mark-redex"],
            ["examples/normal_form.txt", "--show", "M2", "--system", "nonidem-omega"],
            ["examples/normal_form.txt", "--show", "M2", "--width", "60"],
            ["examples/declarations.txt", "--show", "M2", "--fit-declarations"],
            ["examples/declarations.txt", "--show", "N1", "--system", "idem-omega"],
            ["examples/basic.txt", "--show", "M2"],
            ["examples/siam.txt", "--siam", "M"],
            ["examples/reductions.txt", "--show", "B", "--system", "nonidem"],
        ]
        for args in runs:
            with self.subTest(args=args):
                out = io.StringIO()
                with contextlib.redirect_stdout(out):
                    self.assertEqual(main([os.path.join(root, args[0]), "--format", "latex", *args[1:]]), 0)
                bad = sorted({c for c in out.getvalue() if ord(c) > 127})
                self.assertEqual(bad, [])
