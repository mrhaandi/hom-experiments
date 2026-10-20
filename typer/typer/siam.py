"""Sequence types and the Sequence IAM (SIAM).

Following Accattoli, Dal Lago and Vanoni, "The (In)Efficiency of Interaction",
sections 12-13. Sequence types are non-idempotent intersection types where a
multiset is replaced by a sequence:

    A ::= ★ | S -> A        S ::= [A1, ..., An]

with the rules T-Var, T-λ, T-@ (the argument derivations in the order of the
sequence) and T-λ★, which types any abstraction with ★ and has no premises.
In T-λ the sequence of the variable lists the types of its axioms in the
left-to-right order of the derivation (the axiom sequences property).

Derivations here are `Deriv`s in which an `Inter` is read as a sequence (its
order matters) and the rule "lamstar" is T-λ★.

The SIAM moves over a fixed derivation. A state is a judgement (a node), an
occurrence of ★ in the type on the right of its |- (a path into that type),
and a direction: up (towards the premises) or down (towards the conclusion).
"""

from __future__ import annotations

from dataclasses import dataclass, field

from .derive import Deriv, Expander, components
from .itypes import Arrow, Atom, Inter, Type, inter
from .parser import TyperError
from .reduce import WEAK_HEAD, normalize
from .systems import get_system
from .terms import Lam, Term, Var, free_vars, show_term

STAR = Atom("★")
UP, DOWN = "↑", "↓"

# A path to an occurrence of ★ in a type: ("cod",) enters the target of an arrow,
# ("dom", i) the i-th type (from 0) of its sequence.
Step = tuple
Path = tuple[Step, ...]


# --- sequence derivations ---------------------------------------------------------


def to_star(t: Type) -> Type:
    """Every atom becomes ★ (the order of every sequence is kept)."""
    match t:
        case Atom():
            return STAR
        case Arrow(dom, cod):
            return Arrow(to_star(dom), to_star(cod))
        case Inter(parts):
            return Inter(tuple(to_star(p) for p in parts)) if parts else t
    raise TypeError(t)


def star_derivation(d: Deriv) -> Deriv:
    return Deriv(d.rule, d.term, to_star(d.type), tuple(star_derivation(p) for p in d.premises))


def seq(t: Type) -> list[Type]:
    """The sequence of a domain."""
    return components(t) if t != Inter(()) else []


def seq_context(d: Deriv) -> dict[str, list[Type]]:
    match d.rule:
        case "var":
            return {d.term.name: [d.type]}
        case "lamstar":
            return {}
        case "abs":
            c = seq_context(d.premises[0])
            c.pop(d.term.var, None)
            return c
        case "app":
            out: dict[str, list[Type]] = {}
            for p in d.premises:
                for x, ts in seq_context(p).items():
                    out.setdefault(x, []).extend(ts)
            return out
    raise ValueError(d.rule)


def check_sequence(d: Deriv) -> None:
    """Raises TyperError unless d is a sequence type derivation (orders matter)."""

    def fail(msg: str) -> TyperError:
        return TyperError(f"not a sequence type derivation at {d.rule} for {show_term(d.term)}: {msg}")

    match d.rule, d.term:
        case "var", Var():
            pass
        case "lamstar", Lam():
            if d.type != STAR or d.premises:
                raise fail("T-λ★ types an abstraction with ★ and has no premises")
        case "abs", Lam(x, body):
            (p,) = d.premises
            check_sequence(p)
            if not isinstance(d.type, Arrow) or d.type.cod != p.type:
                raise fail("the type must be S -> A with A the type of the body")
            if seq(d.type.dom) != seq_context(p).get(x, []):
                raise fail("the sequence must list the types of the axioms in left-to-right order")
        case "app", _:
            fun, args = d.premises[0], d.premises[1:]
            for p in d.premises:
                check_sequence(p)
            if not isinstance(fun.type, Arrow) or fun.type.cod != d.type:
                raise fail("the function must have type S -> A")
            if seq(fun.type.dom) != [a.type for a in args]:
                raise fail("the arguments must be typed with the sequence, in order")
        case _:
            raise fail("the rule does not match the term")


def weak_head_derivation(t: Term, strategy_note: str = "") -> tuple[Deriv, int]:
    """The derivation of |- t : ★ of the paper for a closed term t: T-λ★ for its weak
    head normal form, expanded back along the weak head reduction. Returns the
    derivation and the number of weak head steps."""
    if free_vars(t):
        raise TyperError(f"the SIAM needs a closed term; {show_term(t)} has free variables {', '.join(sorted(free_vars(t)))}")
    trace = normalize(t, WEAK_HEAD)
    if not isinstance(trace.result, Lam):
        raise TyperError(f"the weak head normal form of a closed term should be an abstraction: {show_term(trace.result)}")
    expander = Expander(get_system("nonidem-omega"), "cbn")
    d = Deriv("lamstar", trace.result, STAR)
    for i in range(trace.steps - 1, -1, -1):
        d = expander.expand(d, trace.terms[i], trace.redexes[i])
    return d, trace.steps


# --- the machine ------------------------------------------------------------------


def star_paths(t: Type, prefix: Path = ()) -> list[Path]:
    """All occurrences of ★ in t, left to right."""
    match t:
        case Atom():
            return [prefix] if t == STAR else []
        case Arrow(dom, cod):
            out = []
            for i, a in enumerate(seq(dom)):
                out.extend(star_paths(a, prefix + (("dom", i),)))
            return out + star_paths(cod, prefix + (("cod",),))
    return []


def rightmost_star(t: Type) -> Path:
    path: Path = ()
    while isinstance(t, Arrow):
        path, t = path + (("cod",),), t.cod
    if t != STAR:
        raise TyperError("the type has no ★ in target position")
    return path


@dataclass
class _Index:
    """Navigation in a derivation: parents, and the axioms of every binder."""

    root: Deriv
    nodes: list[Deriv] = field(default_factory=list)
    parent: dict[int, tuple[int, int]] = field(default_factory=dict)  # node -> (parent, premise index)
    axioms: dict[int, list[int]] = field(default_factory=dict)  # abs node -> its axioms, left to right
    binder: dict[int, tuple[int, int]] = field(default_factory=dict)  # axiom -> (abs node, index)

    def __post_init__(self) -> None:
        def go(d: Deriv, scope: dict[str, int]) -> int:
            n = len(self.nodes)
            self.nodes.append(d)
            if d.rule == "var" and d.term.name in scope:
                b = scope[d.term.name]
                self.binder[n] = (b, len(self.axioms[b]))
                self.axioms[b].append(n)
            if d.rule == "abs":
                self.axioms[n] = []
                scope = {**scope, d.term.var: n}
            for i, p in enumerate(d.premises):
                c = go(p, scope)
                self.parent[c] = (n, i)
            return n

        go(self.root, {})


@dataclass(frozen=True)
class State:
    node: int
    path: Path
    direction: str


@dataclass
class Run:
    derivation: Deriv
    index: _Index
    states: list[State]

    @property
    def visits(self) -> dict[tuple[int, Path], list[tuple[int, str]]]:
        """For every occurrence of ★ (node, path): the steps (from 1) visiting it and their directions."""
        out: dict[tuple[int, Path], list[tuple[int, str]]] = {}
        for k, s in enumerate(self.states, start=1):
            out.setdefault((s.node, s.path), []).append((k, s.direction))
        return out

    def stars(self) -> list[tuple[int, Path]]:
        return [(n, p) for n, d in enumerate(self.index.nodes) for p in star_paths(d.type)]

    def each_star_once(self) -> bool:
        v = self.visits
        return all(len(v.get(s, [])) == 1 for s in self.stars())


def step(ix: _Index, s: State) -> State | None:
    """One SIAM transition (Fig. 8), or None in a final state."""
    d = ix.nodes[s.node]
    p = s.path
    if s.direction == UP:
        match d.rule:
            case "app":  # •1: into the function, the ★ is in its target
                return State(s.node + 1, (("cod",),) + p, UP)
            case "abs":
                if p[0] == ("cod",):  # •2
                    return State(s.node + 1, p[1:], UP)
                _, i = p[0]  # →bt2: to the i-th axiom of the variable
                return State(ix.axioms[s.node][i], p[1:], DOWN)
            case "var":
                if s.node not in ix.binder:
                    return None  # a free variable: final
                b, i = ix.binder[s.node]  # →var: to the binder, i-th type of its sequence
                return State(b, (("dom", i),) + p, DOWN)
            case "lamstar":
                return None
        raise ValueError(d.rule)
    if s.node not in ix.parent:
        return None  # down at the root: final
    par, i = ix.parent[s.node]
    pd = ix.nodes[par]
    if pd.rule == "abs":  # •4
        return State(par, (("cod",),) + p, DOWN)
    children = _children(ix, par)
    if i == 0:
        if p[0] == ("cod",):  # •3
            return State(par, p[1:], DOWN)
        _, k = p[0]  # →arg: into the k-th argument
        return State(children[k + 1], p[1:], UP)
    return State(children[0], (("dom", i - 1),) + p, UP)  # →bt1: back to the function


def _children(ix: _Index, n: int) -> list[int]:
    return sorted(c for c, (par, _) in ix.parent.items() if par == n)


def run(d: Deriv, any_type: bool = False, max_steps: int = 100000) -> Run:
    """Runs the SIAM from the conclusion of d, direction up, on ★ (strict) or on the
    rightmost ★ of its type (any_type)."""
    check_sequence(d)
    if any_type:
        start = rightmost_star(d.type)
    elif d.type == STAR:
        start = ()
    else:
        raise TyperError("the SIAM starts on a derivation of |- t : ★ (use --siam-any-type for other types)")
    ix = _Index(d)
    states = [State(0, start, UP)]
    while (nxt := step(ix, states[-1])) is not None:
        states.append(nxt)
        if len(states) > max_steps:
            raise TyperError(f"the SIAM did not stop within {max_steps} steps")
    return Run(d, ix, states)


# --- rendering --------------------------------------------------------------------


def annotations(r: Run) -> dict[int, dict[Path, str]]:
    """node -> path -> "↑3" (several visits are joined with commas)."""
    out: dict[int, dict[Path, str]] = {}
    for (n, p), vs in r.visits.items():
        out.setdefault(n, {})[p] = ",".join(f"{dr}{k}" for k, dr in vs)
    return out


def show_seq_type(t: Type, ann: dict[Path, str] | None = None, prefix: Path = ()) -> str:
    """[A1, ..., An] -> A, with the ★ at annotated paths followed by their visits."""
    ann = ann or {}
    match t:
        case Atom():
            mark = ann.get(prefix)
            return t.name + (mark or "")
        case Arrow(dom, cod):
            items = [show_seq_type(a, ann, prefix + (("dom", i),)) for i, a in enumerate(seq(dom))]
            return f"[{', '.join(items)}] -> {show_seq_type(cod, ann, prefix + (('cod',),))}"
    raise TypeError(t)


def seq_judgement(d: Deriv, ann: dict[Path, str] | None = None) -> str:
    ctx = ", ".join(f"{x} : [{', '.join(show_seq_type(t) for t in ts)}]" for x, ts in sorted(seq_context(d).items()))
    return f"{ctx + ' ' if ctx else ''}|- {show_term(d.term)} : {show_seq_type(d.type, ann)}"


def show_run(r: Run) -> str:
    """The derivation, conclusion first, with every ★ on the right of |- annotated by its visits."""
    ann = annotations(r)
    lines: list[str] = []
    for n, d in enumerate(r.index.nodes):
        depth, m = 0, n
        while m in r.index.parent:
            m = r.index.parent[m][0]
            depth += 1
        rule = {"abs": "T-λ", "app": "T-@", "var": "T-Var", "lamstar": "T-λ★"}[d.rule]
        lines.append(f"{'  ' * depth}({rule}) {seq_judgement(d, ann.get(n))}")
    return "\n".join(lines)


def summary(r: Run, latex: bool = False) -> str:
    stars = len(r.stars())
    once = "yes" if r.each_star_once() else "no"
    star, iam = (r"$\star$", r"$\lambda$IAM") if latex else ("★", "λIAM")
    return f"{len(r.states)} states; {stars} occurrences of {star} (the {iam} weight); each visited exactly once: {once}"
