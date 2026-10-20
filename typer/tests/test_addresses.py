import unittest

from typer.addresses import addresses, parse_address, show_address, subterm_at
from typer.parser import TyperError, parse_term
from typer.terms import show_term

M = parse_term("fun x y. x (fun z. z y) y")


def at(addr: str) -> str:
    return show_term(subterm_at(M, parse_address(addr)))


class Addresses(unittest.TestCase):
    def test_root(self):
        self.assertEqual(at(""), "fun x y. x (fun z. z y) y")
        self.assertEqual(at("ε"), at(""))
        self.assertEqual(at("eps"), at(""))

    def test_zero_strips_one_binder(self):
        self.assertEqual(at("0"), "fun y. x (fun z. z y) y")
        self.assertEqual(at("0^2"), "x (fun z. z y) y")
        self.assertEqual(at("0,0"), at("0^2"))

    def test_application_head_and_arguments(self):
        self.assertEqual(at("0^3"), "x")
        self.assertEqual(at("0^2,1"), "fun z. z y")
        self.assertEqual(at("0^2,2"), "y")
        self.assertEqual(at("0^2,1,0,1"), "y")

    def test_lone_variable_and_its_head_coincide(self):
        self.assertEqual(at("0^2,2,0"), "y")

    def test_out_of_range(self):
        with self.assertRaises(TyperError):
            at("0^2,3")
        with self.assertRaises(TyperError):
            at("1")

    def test_only_normal_forms(self):
        with self.assertRaises(TyperError):
            subterm_at(parse_term("(fun x. x) y"), ())

    def test_listing_round_trips(self):
        table = addresses(M)
        self.assertEqual(len(table), 9)
        for addr, sub in table:
            self.assertEqual(subterm_at(M, parse_address(show_address(addr))), sub)

    def test_show(self):
        self.assertEqual(show_address(()), "ε")
        self.assertEqual(show_address((0, 0, 1, 0, 0)), "0^2,1,0^2")
        self.assertEqual(show_address((1, 1)), "1,1")


if __name__ == "__main__":
    unittest.main()
