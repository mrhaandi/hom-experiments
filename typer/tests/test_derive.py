import unittest

from typer.derive import Deriv, DerivationError, Expander, canonical, check, context
from typer.itypes import OMEGA, Arrow, Atom
from typer.parser import TyperError, parse_term, parse_type
from typer.reduce import normalize
from typer.systems import SYSTEMS, get_system
from typer.terms import Var

T = parse_term
I = "(fun z. z)"
TERMS = {
    "example": "(fun x. x) (fun y. y)",
    "normal_form": f"(fun f x y. f y x) (fun a b. a (b b)) ({I} {I})",
    "church": "(fun f x. f (f x)) (fun f x. f (f x)) (fun x. x)",
    "K_free": f"(fun x y. x) z ({I} w)",
    "duplication": "(fun x. x x) (fun y. y)",
    "open": "fun q. (fun x. x x) (fun y. q y)",
    "shadowing": "(fun x. (fun x. x) x) w",
    "renaming": "(fun x y. x y) y",
    "erase_bound": "fun q. q ((fun x y. y) q)",
    "erase_app": "(fun q. (fun x y. y) q) w",
}


def run(term: str, system: str, strategy: str):
    tr = normalize(T(term), strategy)
    return tr, Expander(get_system(system), strategy).along(tr)


class Canonical(unittest.TestCase):
    def test_atoms_are_indexed_by_addresses(self):
        d = canonical(T("fun y. y (fun z. z)"), get_system("idem"))
        a0, a010 = Atom("a_{0}"), Atom("a_{0,1,0}")
        self.assertEqual(d.type, Arrow(Arrow(Arrow(a010, a010), a0), a0))

    def test_lone_variable(self):
        d = canonical(T("x"), get_system("idem"))
        self.assertEqual(d, Deriv("var", Var("x"), Atom("a_{ε}")))

    def test_unused_variable(self):
        t = T("fun x y. y")
        self.assertEqual(canonical(t, get_system("idem-omega")).type.dom, OMEGA)
        self.assertEqual(canonical(t, get_system("idem")).type.dom, Atom("a_{ε}"))

    def test_free_variables_in_context(self):
        d = canonical(T("x x"), get_system("nonidem"))
        self.assertEqual(len(context(d, get_system("nonidem"))["x"]), 2)


class Expansion(unittest.TestCase):
    def test_every_derivation_checks(self):
        for system in SYSTEMS:
            for strategy in ("cbn", "cbv"):
                for name, term in TERMS.items():
                    with self.subTest(system=system, strategy=strategy, term=name):
                        tr, ds = run(term, system, strategy)
                        self.assertEqual(len(ds), tr.steps + 1)
                        for t, d in zip(tr.terms, ds):
                            self.assertEqual(d.term, t)
                            check(d, get_system(system))

    def test_with_omega_type_and_context_are_preserved(self):
        for system in ("idem-omega", "nonidem-omega"):
            s = get_system(system)
            for strategy in ("cbn", "cbv"):
                for name, term in TERMS.items():
                    with self.subTest(system=system, strategy=strategy, term=name):
                        _, ds = run(term, system, strategy)
                        for d in ds:
                            self.assertEqual(d.type, ds[-1].type)
                            self.assertEqual(context(d, s), context(ds[-1], s))

    def test_nonidempotent_size_decreases_along_normal_order(self):
        for name, term in TERMS.items():
            with self.subTest(term=name):
                _, ds = run(term, "nonidem-omega", "cbn")
                sizes = [d.size for d in ds]
                self.assertTrue(all(a > b for a, b in zip(sizes, sizes[1:])), sizes)

    def test_without_omega_erased_argument_is_typed(self):
        _, ds = run(f"(fun x y. y) ({I} w)", "nonidem", "cbn")
        self.assertIn("w", context(ds[0], get_system("nonidem")))
        _, ds = run(f"(fun x y. y) ({I} w)", "nonidem-omega", "cbn")
        self.assertNotIn("w", context(ds[0], get_system("nonidem-omega")))

    def test_without_omega_erased_argument_must_normalize(self):
        with self.assertRaises(TyperError):
            run("(fun x y. y) ((fun x. x x) (fun x. x x))", "idem", "cbn")


class Checker(unittest.TestCase):
    def test_rejects_wrong_domain(self):
        s = get_system("nonidem")
        a = Atom("a")
        body = Deriv("var", Var("x"), a)
        bad = Deriv("abs", T("fun x. x"), Arrow(parse_type("a /\\ a"), a), (body,))
        with self.assertRaises(DerivationError):
            check(bad, s)
        check(bad, get_system("idem"))  # a /\ a = a when idempotent

    def test_rejects_missing_argument_without_omega(self):
        a = Atom("a")
        lam = Deriv("abs", T("fun x. y"), Arrow(OMEGA, a), (Deriv("var", Var("y"), a),))
        app = Deriv("app", T("(fun x. y) z"), a, (lam,))
        check(app, get_system("idem-omega"))
        with self.assertRaises(DerivationError):
            check(app, get_system("idem"))


if __name__ == "__main__":
    unittest.main()


class Declarations(unittest.TestCase):
    def fit(self, term, decls, system):
        from typer.derive import fit_declarations

        s = get_system(system)
        d = fit_declarations(canonical(T(term), s), {x: parse_type(t) for x, t in decls.items()}, s)
        check(d, s)
        return d

    def test_fits_the_example(self):
        for system in SYSTEMS:
            d = self.fit("v v", {"v": "a /\\ (a -> a)"}, system)
            self.assertEqual(d.type, Atom("a"))

    def test_multiplicities_matter_only_when_non_idempotent(self):
        self.fit("v v", {"v": "(a -> a) /\\ a /\\ a"}, "idem")
        with self.assertRaises(TyperError):
            self.fit("v v", {"v": "(a -> a) /\\ a /\\ a"}, "nonidem")

    def test_impossible_declaration(self):
        with self.assertRaises(TyperError):
            self.fit("v v", {"v": "a"}, "idem")

    def test_expansion_keeps_declared_types(self):
        s = get_system("idem-omega")
        tr = normalize(T("(fun x. u (fun y. x y)) (fun z. z)"), "cbn")
        ds = Expander(s).along(tr, {"u": parse_type("(b -> b) -> c")})
        for d in ds:
            check(d, s)
            self.assertEqual(context(d, s)["u"], [parse_type("(b -> b) -> c")])
