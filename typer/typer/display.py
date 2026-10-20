"""Plain-text rendering of derivations.

Each judgement is printed on its own line, the conclusion first and its
premises indented below it:

    (app) y : (a -> b) /\\ a |- y y : b
      (var) y : a -> b |- y : a -> b
      (var) y : a |- y : a
"""

from __future__ import annotations

from .derive import Deriv, context, show_context
from .itypes import show_type
from .systems import System
from .terms import show_term


def judgement(d: Deriv, system: System) -> str:
    ctx = show_context(context(d, system))
    return f"{ctx + ' ' if ctx else ''}|- {show_term(d.term)} : {show_type(d.type)}"


def show_derivation(d: Deriv, system: System, indent: str = "") -> str:
    lines: list[str] = []

    def go(d: Deriv, depth: int) -> None:
        lines.append(f"{indent}{'  ' * depth}({d.rule}) {judgement(d, system)}")
        for p in d.premises:
            go(p, depth + 1)

    go(d, 0)
    return "\n".join(lines)
