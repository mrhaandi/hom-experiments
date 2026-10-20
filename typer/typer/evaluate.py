"""Evaluation of a parsed program: NF(...) markers are replaced by normal forms.

The reduction of every definition of the form `M = NF(t)` is kept, so that its
intermediate terms can be numbered and, later, given derivations.
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .parser import Canonical, Program, TyperError
from .reduce import DEFAULT_MAX_STEPS, Trace, is_normal, normalize
from .systems import System, SystemTypeError
from .terms import NF, App, Lam, Term, Var, show_term


@dataclass
class Evaluated:
    program: Program
    system: System
    strategy: str
    max_steps: int = DEFAULT_MAX_STEPS
    defs: dict[str, Term] = field(default_factory=dict)
    traces: dict[str, Trace] = field(default_factory=dict)
    canonical: list[tuple[Canonical, Term]] = field(default_factory=list)


def _line_of(prog: Program, name: str) -> int | None:
    for s in prog.statements:
        if getattr(s, "name", None) == name:
            return s.line
    return None


def evaluate(prog: Program, system: System, strategy: str = "cbn", max_steps: int = DEFAULT_MAX_STEPS) -> Evaluated:
    ev = Evaluated(prog, system, strategy, max_steps)

    for var, ty in prog.env.items():
        try:
            system.check(ty)
        except SystemTypeError as e:
            line = next(s.line for s in prog.statements if getattr(s, "var", None) == var)
            raise TyperError(f"type of {var!r}: {e}", line) from None

    def nf(t: Term, line: int | None) -> Term:
        match t:
            case Var():
                return t
            case Lam(v, body):
                return Lam(v, nf(body, line))
            case App(f, a):
                return App(nf(f, line), nf(a, line))
            case NF(inner):
                try:
                    return normalize(nf(inner, line), strategy, max_steps).result
                except TyperError as e:
                    raise TyperError(e.msg, line) from None
        raise TypeError(t)

    for name, t in prog.defs.items():
        line = _line_of(prog, name)
        if isinstance(t, NF):
            start = nf(t.term, line)
            try:
                trace = normalize(start, strategy, max_steps)
            except TyperError as e:
                raise TyperError(f"{name}: {e.msg}", line) from None
            ev.traces[name] = trace
            ev.defs[name] = trace.result
        else:
            ev.defs[name] = nf(t, line)

    for c in prog.commands:
        t = nf(c.term, c.line)
        if not is_normal(t):
            raise TyperError(f"cannonical: {c.source} is not in normal form: {show_term(t)}", c.line)
        ev.canonical.append((c, t))
    return ev
