"""Intersection types as written in the input file.

An intersection keeps its components as a tuple; whether it is read as a set
(idempotent systems) or a multiset (non-idempotent systems) is decided by the
system, not by the syntax. Omega is the empty intersection.
"""

from __future__ import annotations

from dataclasses import dataclass


class Type:
    def __str__(self) -> str:
        return show_type(self)


@dataclass(frozen=True, eq=True)
class Atom(Type):
    name: str

    __str__ = Type.__str__


@dataclass(frozen=True, eq=True)
class Arrow(Type):
    dom: Type
    cod: Type

    __str__ = Type.__str__


@dataclass(frozen=True, eq=True)
class Inter(Type):
    """A1 /\\ ... /\\ An with n >= 2; n == 0 is omega."""

    parts: tuple[Type, ...]

    __str__ = Type.__str__


OMEGA = Inter(())


def inter(parts: list[Type]) -> Type:
    """Flattens nested intersections; a single component is returned as is."""
    flat: list[Type] = []
    for p in parts:
        flat.extend(p.parts if isinstance(p, Inter) else [p])
    return flat[0] if len(flat) == 1 else Inter(tuple(flat))


def show_type(t: Type) -> str:
    match t:
        case Atom(name):
            return name
        case Inter(()):
            return "omega"
        case Inter(parts):
            return " /\\ ".join(_show_inter_part(p) for p in parts)
        case Arrow(dom, cod):
            d = show_type(dom)
            if isinstance(dom, Arrow):
                d = f"({d})"
            return f"{d} -> {show_type(cod)}"
    raise TypeError(t)


def _show_inter_part(t: Type) -> str:
    s = show_type(t)
    return f"({s})" if isinstance(t, (Arrow, Inter)) and t != OMEGA else s
