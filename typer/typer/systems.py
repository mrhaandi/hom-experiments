"""The four intersection type systems.

All four use strict types: an intersection (or omega) may appear only as the
domain of an arrow or as the whole type of a variable, never as the codomain
of an arrow.

- idempotent: an intersection is a set, so A /\\ A = A (Coppo-Dezani style);
- non-idempotent: an intersection is a multiset, so A /\\ A != A
  (de Carvalho / Gardner style, multiplicities count uses);
- with omega: the empty intersection omega is a type;
- without omega: omega is not allowed anywhere.
"""

from __future__ import annotations

from dataclasses import dataclass

from .itypes import OMEGA, Arrow, Atom, Inter, Type, show_type


class SystemTypeError(Exception):
    """A type that is not allowed in the chosen system."""


@dataclass(frozen=True)
class System:
    idempotent: bool
    omega: bool

    @property
    def name(self) -> str:
        return ("idem" if self.idempotent else "nonidem") + ("-omega" if self.omega else "")

    def __str__(self) -> str:
        return self.name

    # types

    def check(self, t: Type) -> None:
        """Raises SystemTypeError if t is not a type of this system."""
        self._check(t, top=True)

    def _check(self, t: Type, top: bool) -> None:
        match t:
            case Atom():
                return
            case Inter(parts):
                if not top:
                    raise SystemTypeError(f"intersection {show_type(t)} on the right of an arrow (types are strict)")
                if not parts and not self.omega:
                    raise SystemTypeError(f"omega is not allowed in system {self.name}")
                for p in parts:
                    self._check(p, top=False)
            case Arrow(dom, cod):
                self._check(dom, top=True)
                self._check(cod, top=False)

    def norm(self, t: Type) -> Type:
        """Canonical representative: intersections sorted, and deduplicated if idempotent."""
        match t:
            case Atom():
                return t
            case Arrow(dom, cod):
                return Arrow(self.norm(dom), self.norm(cod))
            case Inter(parts):
                ps = sorted((self.norm(p) for p in parts), key=show_type)
                if self.idempotent:
                    ps = [p for i, p in enumerate(ps) if i == 0 or p != ps[i - 1]]
                if len(ps) == 1:
                    return ps[0]
                return Inter(tuple(ps)) if ps else OMEGA
        raise TypeError(t)

    def equal(self, s: Type, t: Type) -> bool:
        return self.norm(s) == self.norm(t)


SYSTEMS = {s.name: s for s in (System(i, o) for i in (True, False) for o in (False, True))}
DEFAULT_SYSTEM = "idem"


def get_system(name: str) -> System:
    try:
        return SYSTEMS[name]
    except KeyError:
        raise ValueError(f"unknown system {name!r}, choose one of {', '.join(SYSTEMS)}") from None
