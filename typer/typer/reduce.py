"""Beta-reduction to normal form under the two strategies.

Both strategies reduce under abstractions, so both reach the full beta-normal
form when they terminate:

- cbn: normal order, always the leftmost-outermost redex;
- cbv: applicative order, the leftmost-innermost redex, so an argument is
  normalised before the redex it belongs to is contracted.

A position is a path from the root: "f" (function of an application),
"a" (argument), "b" (body of an abstraction).
"""

from __future__ import annotations

from dataclasses import dataclass

from .parser import TyperError
from .terms import NF, App, Lam, Term, subst

STRATEGIES = ("cbn", "cbv")
WEAK_HEAD = "whn"  # weak head reduction (the SIAM's evaluation), used internally
DEFAULT_MAX_STEPS = 1000

Position = tuple[str, ...]


def is_redex(t: Term) -> bool:
    return isinstance(t, App) and isinstance(t.fun, Lam)


def is_normal(t: Term) -> bool:
    match t:
        case App(fun, arg):
            return not isinstance(fun, Lam) and is_normal(fun) and is_normal(arg)
        case Lam(_, body):
            return is_normal(body)
        case NF():
            return False
    return True


def contract(redex: Term) -> Term:
    assert isinstance(redex, App) and isinstance(redex.fun, Lam)
    return subst(redex.fun.body, redex.fun.var, redex.arg)


def _find_cbn(t: Term, pos: Position) -> Position | None:
    match t:
        case App(fun, arg):
            if isinstance(fun, Lam):
                return pos
            return _find_cbn(fun, pos + ("f",)) or _find_cbn(arg, pos + ("a",))
        case Lam(_, body):
            return _find_cbn(body, pos + ("b",))
    return None


def _find_cbv(t: Term, pos: Position) -> Position | None:
    match t:
        case App(fun, arg):
            inner = _find_cbv(fun, pos + ("f",)) or _find_cbv(arg, pos + ("a",))
            if inner is not None:
                return inner
            return pos if isinstance(fun, Lam) else None
        case Lam(_, body):
            return _find_cbv(body, pos + ("b",))
    return None


def _find_whn(t: Term, pos: Position) -> Position | None:
    if isinstance(t, App):
        return pos if isinstance(t.fun, Lam) else _find_whn(t.fun, pos + ("f",))
    return None


def find_redex(t: Term, strategy: str) -> Position | None:
    """The position of the next redex, or None if t is normal (for "whn": weak head normal)."""
    if strategy == "whn":
        return _find_whn(t, ())
    if strategy == "cbn":
        return _find_cbn(t, ())
    if strategy == "cbv":
        return _find_cbv(t, ())
    raise ValueError(f"unknown strategy {strategy!r}")


def subterm(t: Term, pos: Position) -> Term:
    for p in pos:
        match p, t:
            case "f", App(fun, _):
                t = fun
            case "a", App(_, arg):
                t = arg
            case "b", Lam(_, body):
                t = body
            case _:
                raise ValueError(f"bad position {pos} in {t}")
    return t


def replace(t: Term, pos: Position, new: Term) -> Term:
    if not pos:
        return new
    head, rest = pos[0], pos[1:]
    match head, t:
        case "f", App(fun, arg):
            return App(replace(fun, rest, new), arg)
        case "a", App(fun, arg):
            return App(fun, replace(arg, rest, new))
        case "b", Lam(var, body):
            return Lam(var, replace(body, rest, new))
    raise ValueError(f"bad position {pos} in {t}")


@dataclass(frozen=True)
class Trace:
    """A reduction t0 -> t1 -> ... -> tn; redexes[i] is the position contracted in terms[i]."""

    strategy: str
    terms: tuple[Term, ...]
    redexes: tuple[Position, ...]

    @property
    def result(self) -> Term:
        return self.terms[-1]

    @property
    def steps(self) -> int:
        return len(self.redexes)


def normalize(t: Term, strategy: str = "cbn", max_steps: int = DEFAULT_MAX_STEPS) -> Trace:
    if strategy not in STRATEGIES + (WEAK_HEAD,):
        raise ValueError(f"unknown strategy {strategy!r}")
    terms, redexes = [t], []
    while (pos := find_redex(t, strategy)) is not None:
        if len(redexes) >= max_steps:
            raise TyperError(
                f"no normal form reached after {max_steps} {strategy} steps "
                f"(the term may have no normal form, or use --max-steps)"
            )
        t = replace(t, pos, contract(subterm(t, pos)))
        terms.append(t)
        redexes.append(pos)
    return Trace(strategy, tuple(terms), tuple(redexes))
