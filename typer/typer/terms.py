"""Untyped lambda-terms."""

from __future__ import annotations

from dataclasses import dataclass
from itertools import count


class Term:
    def __str__(self) -> str:
        return show_term(self)


@dataclass(frozen=True, eq=True)
class Var(Term):
    name: str

    __str__ = Term.__str__


@dataclass(frozen=True, eq=True)
class Lam(Term):
    var: str
    body: Term

    __str__ = Term.__str__


@dataclass(frozen=True, eq=True)
class App(Term):
    fun: Term
    arg: Term

    __str__ = Term.__str__


@dataclass(frozen=True, eq=True)
class NF(Term):
    """Marker: the beta-normal form of `term`. Computed during evaluation."""

    term: Term

    __str__ = Term.__str__


def free_vars(t: Term) -> frozenset[str]:
    match t:
        case Var(name):
            return frozenset({name})
        case Lam(var, body):
            return free_vars(body) - {var}
        case App(fun, arg):
            return free_vars(fun) | free_vars(arg)
        case NF(term):
            return free_vars(term)
    raise TypeError(t)


def all_vars(t: Term) -> frozenset[str]:
    match t:
        case Var(name):
            return frozenset({name})
        case Lam(var, body):
            return all_vars(body) | {var}
        case App(fun, arg):
            return all_vars(fun) | all_vars(arg)
        case NF(term):
            return all_vars(term)
    raise TypeError(t)


def fresh(base: str, avoid: frozenset[str] | set[str]) -> str:
    """A variant of `base` (base', base'', ...) not in `avoid`."""
    stem = base.rstrip("'")
    for i in count(1):
        cand = stem + "'" * i
        if cand not in avoid:
            return cand
    raise AssertionError


def subst(t: Term, x: str, s: Term) -> Term:
    """Capture-avoiding substitution t[x := s]."""
    match t:
        case Var(name):
            return s if name == x else t
        case App(fun, arg):
            return App(subst(fun, x, s), subst(arg, x, s))
        case NF(term):
            return NF(subst(term, x, s))
        case Lam(var, body):
            if var == x or x not in free_vars(body):
                return t
            fs = free_vars(s)
            if var in fs:
                new = fresh(var, fs | all_vars(body) | {x})
                body = subst(body, var, Var(new))
                var = new
            return Lam(var, subst(body, x, s))
    raise TypeError(t)


def alpha_eq(t: Term, u: Term) -> bool:
    """Equality up to renaming of bound variables."""

    def go(t: Term, u: Term, env_t: dict[str, int], env_u: dict[str, int], depth: int) -> bool:
        match t, u:
            case Var(a), Var(b):
                if a in env_t or b in env_u:
                    return env_t.get(a) == env_u.get(b)
                return a == b
            case Lam(x, b1), Lam(y, b2):
                return go(b1, b2, {**env_t, x: depth}, {**env_u, y: depth}, depth + 1)
            case App(f1, a1), App(f2, a2):
                return go(f1, f2, env_t, env_u, depth) and go(a1, a2, env_t, env_u, depth)
            case NF(a), NF(b):
                return go(a, b, env_t, env_u, depth)
        return False

    return go(t, u, {}, {}, 0)


def show_term(t: Term, mark: tuple[str, ...] | None = None) -> str:
    """Prints in the input syntax: fun x y. body, left-associative application.

    If `mark` is a position (see reduce.py), that subterm is printed in [ ].
    """

    def go(t: Term, pos: tuple[str, ...]) -> str:
        s = inner(t, pos)
        return f"[{s}]" if mark is not None and pos == mark else s

    def inner(t: Term, pos: tuple[str, ...]) -> str:
        match t:
            case Var(name):
                return name
            case NF(term):
                return f"NF({go(term, pos)})"
            case Lam():
                vars_ = []
                while True:
                    vars_.append(t.var)
                    t, pos = t.body, pos + ("b",)
                    if not isinstance(t, Lam) or pos == mark:
                        break
                return f"fun {' '.join(vars_)}. {go(t, pos)}"
            case App(fun, arg):
                f = go(fun, pos + ("f",))
                if isinstance(fun, Lam) and pos + ("f",) != mark:
                    f = f"({f})"
                a = go(arg, pos + ("a",))
                if isinstance(arg, (Lam, App)) and pos + ("a",) != mark:
                    a = f"({a})"
                return f"{f} {a}"
        raise TypeError(t)

    return go(t, ())
