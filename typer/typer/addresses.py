"""Addresses of subterms of normal forms.

The root has the empty address. If the subterm at address p is

- an application y M1 ... Mk (with y a variable and k maximal), then p,0 is
  the head y and p,i is Mi for 1 <= i <= k;
- an abstraction fun x0 ... xk. M, then p,0 is fun x1 ... xk. M, that is,
  p,0^j strips the first j binders and p,0^(k+1) is M.

For a lone variable (k = 0) p and p,0 denote the same occurrence; the
address p is the canonical one. Addresses are written as comma-separated
numbers, with 0^j abbreviating j zeros, e.g. "0^2,1,0"; the root is written
as "", "ε" or "eps".
"""

from __future__ import annotations

import re

from .parser import TyperError
from .reduce import Position, is_normal, subterm
from .terms import App, Lam, Term, Var

Address = tuple[int, ...]


def spine(t: Term) -> tuple[Term, list[Term]]:
    """y M1 ... Mk  ->  (y, [M1, ..., Mk])."""
    args = []
    while isinstance(t, App):
        args.append(t.arg)
        t = t.fun
    return t, args[::-1]


def to_position(t: Term, addr: Address) -> Position:
    """The internal path (f/a/b, see reduce.py) of the subterm at `addr`."""
    if not is_normal(t):
        raise TyperError("addresses are defined only for normal forms")
    pos: list[str] = []
    for n, i in enumerate(addr):
        if isinstance(t, Lam):
            if i != 0:
                raise TyperError(f"address {show_address(addr)}: at {show_address(addr[:n])} there is an abstraction, only 0 is allowed")
            t = t.body
            pos.append("b")
            continue
        head, args = spine(t)
        if i > len(args):
            raise TyperError(
                f"address {show_address(addr)}: the application at {show_address(addr[:n])} has only {len(args)} argument(s)"
            )
        # The argument Mi sits below k - i function nodes, then one argument edge.
        if i == 0:
            pos.extend(["f"] * len(args))
            t = head
        else:
            pos.extend(["f"] * (len(args) - i) + ["a"])
            t = args[i - 1]
    return tuple(pos)


def subterm_at(t: Term, addr: Address) -> Term:
    return subterm(t, to_position(t, addr))


def addresses(t: Term) -> list[tuple[Address, Term]]:
    """All addressed subterms of a normal form, in prefix order (lone variables listed once)."""
    out: list[tuple[Address, Term]] = []

    def go(t: Term, addr: Address) -> None:
        out.append((addr, t))
        if isinstance(t, Lam):
            go(t.body, addr + (0,))
            return
        head, args = spine(t)
        if args:
            out.append((addr + (0,), head))
            for i, a in enumerate(args, start=1):
                go(a, addr + (i,))

    if not is_normal(t):
        raise TyperError("addresses are defined only for normal forms")
    go(t, ())
    return out


_ADDR_PART = re.compile(r"^(\d+)(?:\^(\d+))?$")


def parse_address(s: str) -> Address:
    s = s.strip()
    if s in ("", "ε", "eps"):
        return ()
    out: list[int] = []
    for part in s.split(","):
        m = _ADDR_PART.match(part.strip())
        if not m:
            raise TyperError(f"bad address {s!r}: expected numbers separated by commas, e.g. 0^2,1")
        n, rep = int(m.group(1)), int(m.group(2) or 1)
        out.extend([n] * rep)
    return tuple(out)


def show_address(addr: Address) -> str:
    """Compact form: runs of zeros longer than one become 0^j."""
    if not addr:
        return "ε"
    parts: list[str] = []
    i = 0
    while i < len(addr):
        j = i
        while j < len(addr) and addr[j] == addr[i]:
            j += 1
        run = j - i
        if addr[i] == 0 and run > 1:
            parts.append(f"0^{run}")
        else:
            parts.extend([str(addr[i])] * run)
        i = j
    return ",".join(parts)
