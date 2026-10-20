"""Type derivations: canonical derivations of normal forms, subject expansion, checking.

A derivation is a tree of three rules over strict types (atoms and arrows):

    var   x : [A] |- x : A
    abs   from  G, x : [A1..An] |- M : B   infer  G |- fun x. M : A1 /\\ ... /\\ An -> B
    app   from  G |- M : A1 /\\ ... /\\ An -> B  and  Di |- N : Ai (i = 1..n)
          infer  G + D1 + ... + Dn |- M N : B

Contexts are computed from the leaves, never stored. In non-idempotent systems
the domain A1 /\\ ... /\\ An and the contexts are multisets, so the argument
of an application has exactly one derivation per component of the domain.
In idempotent systems they are sets; an argument may then have several
derivations with the same type (for example copies with different contexts),
as long as their types are exactly the components of the domain.

With omega, n = 0 is allowed: an abstraction whose variable is not used gets
domain omega and its argument has no derivation. Without omega, n >= 1: such
an abstraction gets one arbitrary domain type and its argument is typed once.
"""

from __future__ import annotations

from dataclasses import dataclass, field
from itertools import count

from .addresses import Address, show_address, spine
from .itypes import OMEGA, Arrow, Atom, Inter, Type, inter, show_type
from .parser import TyperError
from .reduce import DEFAULT_MAX_STEPS, Position, Trace, normalize
from .systems import System, SystemTypeError
from .terms import App, Lam, Term, Var, free_vars, show_term


@dataclass(frozen=True)
class Deriv:
    rule: str  # "var", "abs" or "app"
    term: Term
    type: Type
    premises: tuple["Deriv", ...] = ()

    @property
    def size(self) -> int:
        return 1 + sum(p.size for p in self.premises)


Context = dict[str, list[Type]]


def components(t: Type) -> list[Type]:
    return list(t.parts) if isinstance(t, Inter) else [t]


def domain(types: list[Type], system: System) -> Type:
    """The intersection of `types` as a domain of this system (omega if empty)."""
    if system.idempotent:
        types = _dedup(types, system)
    return inter(types) if types else OMEGA


def _dedup(types: list[Type], system: System) -> list[Type]:
    out: list[Type] = []
    for t in types:
        if not any(system.equal(t, u) for u in out):
            out.append(t)
    return out


def context(d: Deriv, system: System) -> Context:
    match d.rule:
        case "lamstar":
            return {}
        case "var":
            return {d.term.name: [d.type]}
        case "abs":
            c = context(d.premises[0], system)
            c.pop(d.term.var, None)
            return c
        case "app":
            out: Context = {}
            for p in d.premises:
                for x, ts in context(p, system).items():
                    out.setdefault(x, []).extend(ts)
            if system.idempotent:
                out = {x: _dedup(ts, system) for x, ts in out.items()}
            return out
    raise ValueError(d.rule)


def show_context(c: Context) -> str:
    def part(ts: list[Type]) -> str:
        s = show_type(inter(ts))
        return f"({s})" if isinstance(inter(ts), Arrow) and len(ts) > 1 else s

    return ", ".join(f"{x} : {part(ts)}" for x, ts in sorted(c.items()))


# --- checking ------------------------------------------------------------------


class DerivationError(TyperError):
    pass


def check(d: Deriv, system: System) -> None:
    """Raises DerivationError if d is not a derivation of `system`."""

    def fail(msg: str) -> DerivationError:
        return DerivationError(f"{d.rule} rule for {show_term(d.term)} : {show_type(d.type)}: {msg}")

    try:
        system.check(d.type)
    except SystemTypeError as e:
        raise fail(str(e)) from None
    if isinstance(d.type, Inter):
        raise fail("the type of a judgement must be strict (an atom or an arrow)")

    match d.rule, d.term:
        case "var", Var():
            if d.premises:
                raise fail("var has no premises")
        case "abs", Lam(x, body):
            if len(d.premises) != 1 or d.premises[0].term != body:
                raise fail("the premise must type the body")
            (p,) = d.premises
            check(p, system)
            if not isinstance(d.type, Arrow) or not system.equal(d.type.cod, p.type):
                raise fail("the type must be D -> B where B is the type of the body")
            used = context(p, system).get(x, [])
            if used:
                if not system.equal(d.type.dom, domain(used, system)):
                    raise fail(f"the domain must be {show_type(domain(used, system))}, the types of {x} in the body")
            elif system.omega:
                if d.type.dom != OMEGA:
                    raise fail(f"{x} is not used, so the domain must be omega")
            elif isinstance(d.type.dom, Inter):
                raise fail(f"{x} is not used, so the domain must be a single type")
        case "app", App(f, a):
            if not d.premises or d.premises[0].term != f:
                raise fail("the first premise must type the function")
            fun, args = d.premises[0], d.premises[1:]
            for p in d.premises:
                check(p, system)
            if not isinstance(fun.type, Arrow) or not system.equal(fun.type.cod, d.type):
                raise fail("the function must have type D -> B where B is the type of the application")
            if any(p.term != a for p in args):
                raise fail("the other premises must type the argument")
            want = components(fun.type.dom)
            got = [p.type for p in args]
            if not system.omega and not got:
                raise fail("without omega the argument must be typed")
            if system.idempotent:
                ok = system.equal(domain(got, system), domain(want, system)) if got else fun.type.dom == OMEGA
            else:
                ok = system.equal(inter(got) if got else OMEGA, fun.type.dom)
            if not ok:
                raise fail(f"the argument has types {[show_type(t) for t in got]}, the domain is {show_type(fun.type.dom)}")
        case _:
            raise fail("the rule does not match the shape of the term")


# --- canonical derivations ------------------------------------------------------------


def atom(prefix: str, addr: Address) -> Atom:
    return Atom(f"{prefix}_{{{show_address(addr)}}}")


def canonical(t: Term, system: System, prefix: str = "a") -> Deriv:
    """The canonical derivation of a normal form.

    The application y M1 ... Mk at address p gets the atom a_{p}, its head y
    gets T1 -> ... -> Tk -> a_{p}, where Ti is the type of Mi; an abstraction
    collects the types of its variable. Without omega an unused variable of the
    abstraction at address p gets the atom a_{p}.
    """

    def go(t: Term, addr: Address) -> Deriv:
        if isinstance(t, Lam):
            body = go(t.body, addr + (0,))
            used = context(body, system).get(t.var, [])
            if used:
                dom = domain(used, system)
            else:
                dom = OMEGA if system.omega else atom(prefix, addr)
            return Deriv("abs", t, Arrow(dom, body.type), (body,))
        head, args = spine(t)
        if not isinstance(head, Var):
            raise TyperError(f"not a normal form: {show_term(t)}")
        arg_ds = [go(m, addr + (i,)) for i, m in enumerate(args, start=1)]
        result = atom(prefix, addr)
        ty = result
        for ad in reversed(arg_ds):
            ty = Arrow(ad.type, ty)
        d = Deriv("var", head, ty)
        for m, ad in zip(args, arg_ds):
            d = Deriv("app", App(d.term, m), d.type.cod, (d, ad))
        return d

    return go(t, ())


def fit_declarations(d: Deriv, declarations: dict[str, Type], system: System) -> Deriv:
    """Instantiates the atoms a_{...} of a canonical derivation so that its context matches the declarations.

    For every declared free variable x the types x is used with must become exactly
    the components of its declared type: as a multiset in non-idempotent systems,
    as a set in idempotent ones. Raises TyperError if that is impossible.
    """
    ctx = context(d, system)
    names = sorted(x for x in ctx if x in declarations)
    if not names:
        return d

    def is_var(a: Atom) -> bool:
        return a.name.startswith("a_{")

    if system.idempotent:
        needed = [t for x in names for t in ctx[x]]
        avail = [components(declarations[x]) for x in names for _ in ctx[x]]

        def covers(sub: dict[str, Type]) -> bool:
            return all(
                system.equal(domain([subst_type(t, sub) for t in ctx[x]], system), domain(components(declarations[x]), system))
                for x in names
            )

        sub = _unify_choices(needed, avail, is_var, covers)
    else:
        sub = {}
        for x in names:
            sub = _unify_inter(ctx[x], components(declarations[x]), sub, is_var)
            if sub is None:
                break
    if sub is None:
        uses = "; ".join(f"{x} : {show_type(inter(ctx[x]))}" for x in names)
        decl = "; ".join(f"{x} : {show_type(declarations[x])}" for x in names)
        raise TyperError(f"the canonical typing ({uses}) cannot be fitted to the declarations ({decl})")
    return subst_deriv(d, sub)


# --- subject expansion ------------------------------------------------------------


@dataclass
class Expander:
    """Expands derivations backwards along a reduction (one per program and system)."""

    system: System
    strategy: str = "cbn"
    max_steps: int = DEFAULT_MAX_STEPS
    _prefixes: "count[int]" = field(default_factory=lambda: count(1))

    def fresh_prefix(self) -> str:
        n = next(self._prefixes)
        letters = "bcdefghijklmnopqrstuvwxyz"
        return letters[(n - 1) % 25] + ("" if n <= 25 else str((n - 1) // 25))

    def along(self, trace: Trace, declarations: dict[str, Type] | None = None) -> list[Deriv]:
        """Derivations of every term of the trace: canonical for the last, expanded for the rest.

        With `declarations`, the canonical derivation is first fitted to them (see fit_declarations).
        """
        ds = [canonical(trace.result, self.system)]
        if declarations:
            ds[0] = fit_declarations(ds[0], declarations, self.system)
        for i in range(trace.steps - 1, -1, -1):
            ds.append(self.expand(ds[-1], trace.terms[i], trace.redexes[i]))
        ds.reverse()
        return ds

    def expand(self, d: Deriv, t: Term, pos: Position) -> Deriv:
        """From a derivation of the reduct of t at `pos`, a derivation of t with the same type.

        With omega, and without omega whenever no erased argument uses a variable
        bound above the redex, the context and the type are preserved exactly.
        Otherwise the domain of that binder may have to grow (see _erased).
        """
        binders: dict[str, Deriv] = {}

        def go(d: Deriv, t: Term, pos: Position) -> Deriv:
            if not pos:
                return self._expand_redex(d, t, binders)
            step, rest = pos[0], pos[1:]
            match step, t, d.rule:
                case "b", Lam(x, body), "abs":
                    binders[x] = d
                    child = go(d.premises[0], body, rest)
                    used = context(child, self.system).get(x, [])
                    dom = domain(used, self.system) if used else d.type.dom
                    return Deriv("abs", t, Arrow(dom, child.type), (child,))
                case "f", App(f, a), "app":
                    fun = go(d.premises[0], f, rest)
                    return Deriv("app", t, d.type, (fun, *self._extra_args(d.premises[0], fun, d.premises[1:], a)))
                case "a", App(f, a), "app":
                    args = tuple(go(p, a, rest) for p in d.premises[1:])
                    if any(p.type != q.type for p, q in zip(args, d.premises[1:])):
                        raise TyperError(
                            f"without omega, expanding inside the argument {show_term(a)} changed its type; "
                            f"this case is not supported yet"
                        )
                    return Deriv("app", t, d.type, (d.premises[0], *args))
            raise AssertionError(f"derivation does not follow the term at {step}")

        return go(d, t, pos)

    def _extra_args(self, old: Deriv, new: Deriv, args: tuple[Deriv, ...], arg: Term) -> tuple[Deriv, ...]:
        """Arguments for a function whose domain grew from old.type to new.type, reusing derivations."""
        if old.type == new.type:
            return args
        old_c, new_c = components(old.type.dom), components(new.type.dom)
        if self.system.idempotent:
            if self.system.equal(domain(old_c, self.system), domain(new_c, self.system)):
                return args
            missing = [c for c in new_c if not any(self.system.equal(c, o) for o in old_c)]
        else:
            missing = list(new_c)
            for o in old_c:
                i = next((i for i, c in enumerate(missing) if self.system.equal(c, o)), None)
                if i is None:
                    missing = None
                    break
                missing.pop(i)
        extra = []
        for c in missing or []:
            reuse = next((p for p in args if self.system.equal(p.type, c)), None)
            if reuse is None:
                missing = None
                break
            extra.append(reuse)
        if missing is None:
            raise TyperError(
                f"without omega, the domain of a function applied to {show_term(arg)} had to change "
                f"from {show_type(old.type.dom)} to {show_type(new.type.dom)}; this case is not supported yet"
            )
        return (*args, *extra)

    def _expand_redex(self, d: Deriv, redex: Term, binders: dict[str, Deriv]) -> Deriv:
        assert isinstance(redex, App) and isinstance(redex.fun, Lam)
        x, m, n = redex.fun.var, redex.fun.body, redex.arg
        copies: list[Deriv] = []

        def split(d: Deriv, m: Term, active: bool = True) -> Deriv:
            # d derives m[x := N]; rebuilt along m, since substitution may have renamed binders of m.
            match m:
                case Var(name) if name == x and active:
                    copies.append(d)
                    return Deriv("var", m, d.type)
                case Var():
                    return Deriv("var", m, d.type)
                case Lam() if d.rule == "lamstar":
                    return Deriv("lamstar", m, d.type)
                case Lam(y, body):
                    return Deriv("abs", m, d.type, (split(d.premises[0], body, active and y != x),))
                case App(f, a):
                    fun, args = d.premises[0], d.premises[1:]
                    return Deriv("app", m, d.type, (split(fun, f, active), *(split(p, a, active) for p in args)))
            raise TypeError(m)

        body = split(d, m)
        if self.system.idempotent:
            copies = [c for i, c in enumerate(copies) if c not in copies[:i]]
        if copies:
            dom, args = domain([c.type for c in copies], self.system), copies
        elif self.system.omega:
            dom, args = OMEGA, []
        else:
            arg = self._erased(n, binders)
            dom, args = arg.type, [arg]
        lam = Deriv("abs", redex.fun, Arrow(dom, d.type), (body,))
        return Deriv("app", redex, d.type, (lam, *args))

    def _erased(self, n: Term, binders: dict[str, Deriv]) -> Deriv:
        """Without omega an erased argument still needs a derivation: of its own normal form, expanded.

        Its atoms are fresh. If it uses a variable q bound above the redex, its
        fresh atoms are first unified so that the types of q it needs are among
        the types q already has; only when that fails does the domain of q grow.
        """
        try:
            trace = normalize(n, self.strategy, self.max_steps)
        except TyperError:
            raise TyperError(f"without omega, the erased argument {show_term(n)} must have a normal form") from None
        sub = Expander(self.system, self.strategy, self.max_steps, self._prefixes)
        prefix = self.fresh_prefix()
        d = canonical(trace.result, self.system, prefix)
        for i in range(trace.steps - 1, -1, -1):
            d = sub.expand(d, trace.terms[i], trace.redexes[i])

        captured = sorted(free_vars(n) & set(binders))
        if captured:
            ctx = context(d, self.system)
            needed = [t for q in captured for t in ctx[q]]
            avail = [components(binders[q].type.dom) for q in captured for _ in ctx[q]]
            sub_ = _unify_choices(needed, avail, lambda a: a.name.startswith(prefix + "_{"))
            if sub_ is not None:
                d = subst_deriv(d, sub_)
        return d


# --- type substitution and unification --------------------------------------------


def subst_type(t: Type, sub: dict[str, Type]) -> Type:
    match t:
        case Atom(name):
            return sub.get(name, t)
        case Arrow(dom, cod):
            return Arrow(subst_type(dom, sub), subst_type(cod, sub))
        case Inter(parts):
            return inter([subst_type(p, sub) for p in parts]) if parts else t
    raise TypeError(t)


def subst_deriv(d: Deriv, sub: dict[str, Type]) -> Deriv:
    return Deriv(d.rule, d.term, subst_type(d.type, sub), tuple(subst_deriv(p, sub) for p in d.premises))


def _unify(s: Type, t: Type, sub: dict[str, Type], is_var) -> dict[str, Type] | None:
    s, t = subst_type(s, sub), subst_type(t, sub)
    if s == t:
        return sub
    if isinstance(s, Atom) and is_var(s):
        return None if _occurs(s.name, t) else {**{k: subst_type(v, {s.name: t}) for k, v in sub.items()}, s.name: t}
    if isinstance(t, Atom) and is_var(t):
        return _unify(t, s, sub, is_var)
    match s, t:
        case Arrow(d1, c1), Arrow(d2, c2):
            sub = _unify_inter(components(d1), components(d2), sub, is_var)
            return None if sub is None else _unify(c1, c2, sub, is_var)
    return None


def _unify_inter(xs: list[Type], ys: list[Type], sub, is_var):
    if len(xs) != len(ys):
        return None
    if not xs:
        return sub
    for i, y in enumerate(ys):
        s2 = _unify(xs[0], y, sub, is_var)
        if s2 is not None:
            s3 = _unify_inter(xs[1:], ys[:i] + ys[i + 1:], s2, is_var)
            if s3 is not None:
                return s3
    return None


def _occurs(name: str, t: Type) -> bool:
    match t:
        case Atom(n):
            return n == name
        case Arrow(dom, cod):
            return _occurs(name, dom) or _occurs(name, cod)
        case Inter(parts):
            return any(_occurs(name, p) for p in parts)
    return False


def _unify_choices(needed: list[Type], avail: list[list[Type]], is_var, accept=lambda sub: True) -> dict[str, Type] | None:
    """A substitution making every needed[i] equal to some type in avail[i] and passing `accept`, or None."""

    def go(i: int, sub: dict[str, Type]):
        if i == len(needed):
            return sub if accept(sub) else None
        for a in avail[i]:
            s2 = _unify(needed[i], a, sub, is_var)
            if s2 is not None and (r := go(i + 1, s2)) is not None:
                return r
        return None

    return go(0, {})
