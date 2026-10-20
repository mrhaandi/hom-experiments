"""LaTeX rendering of terms, types, reductions and derivations (bussproofs).

Notation follows the system: idempotent intersections are written A \\cap B
with omega as \\omega; non-idempotent ones as multisets [A, B] with omega as [\\,].
"""

from __future__ import annotations

import re
from dataclasses import dataclass

from .derive import Context, Deriv, context
from .parser import Canonical, Def, Statement, TypeDecl
from .itypes import Arrow, Atom, Inter, Type
from .reduce import Position
from .systems import System
from .terms import NF, App, Lam, Term, Var

MAX_PREMISES = 5  # bussproofs supports at most QuinaryInfC

_GENERATED_ATOM = re.compile(r"^([a-z][0-9]*)_\{(.*)\}$")


_INDEXED_NAME = re.compile(r"^([A-Za-z]+)(\d+)$")


def name_tex(name: str) -> str:
    """x -> x, M2 -> M_{2}, two -> \\mathit{two}; primes are kept."""
    base = name.rstrip("'")
    primes = name[len(base):]
    if m := _INDEXED_NAME.match(base):
        return f"{name_tex(m.group(1))}_{{{m.group(2)}}}{primes}"
    if len(base) == 1:
        return base + primes
    return r"\mathit{" + base.replace("_", r"\_") + "}" + primes


def atom_tex(name: str) -> str:
    m = _GENERATED_ATOM.match(name)
    if m:
        addr = m.group(2).replace("ε", r"\varepsilon")
        return f"{m.group(1)}_{{{addr}}}"
    if name in ("star", "★"):
        return r"\star"
    return name_tex(name)


def term_tex(t: Term, mark: Position | None = None) -> str:
    """Like terms.show_term, with \\lambda; the subterm at `mark` is underlined."""

    def go(t: Term, pos: Position) -> str:
        s = inner(t, pos)
        return rf"\underline{{{s}}}" if mark is not None and pos == mark else s

    def inner(t: Term, pos: Position) -> str:
        match t:
            case Var(name):
                return name_tex(name)
            case NF(term):
                return rf"\mathrm{{NF}}({go(term, pos)})"
            case Lam():
                vars_ = []
                while True:
                    vars_.append(name_tex(t.var))
                    t, pos = t.body, pos + ("b",)
                    if not isinstance(t, Lam) or pos == mark:
                        break
                return rf"\lambda {r'\,'.join(vars_)}.\,{go(t, pos)}"
            case App(fun, arg):
                f = go(fun, pos + ("f",))
                if isinstance(fun, Lam):
                    f = f"({f})"
                a = go(arg, pos + ("a",))
                if isinstance(arg, (Lam, App)):
                    a = f"({a})"
                return rf"{f}\,{a}"
        raise TypeError(t)

    return go(t, ())


@dataclass(frozen=True)
class Style:
    """How types are written when the standard layout does not fit the line.

    stacked: the components of an intersection are written one below the other;
    atoms: short names for atoms (e.g. a_{0,1,0} -> \alpha_{1});
    abbrevs: names for whole types (e.g. \tau_{1}), defined below the derivation.
    """

    stacked: bool = False
    atoms: tuple[tuple[str, str], ...] = ()
    abbrevs: tuple[tuple[Type, str], ...] = ()

    def with_(self, **kw) -> "Style":
        return Style(**{**self.__dict__, **kw})


PLAIN = Style()


def _stack(rows: list[str]) -> str:
    return r"\begin{array}[c]{@{}l@{}}" + r" \\ ".join(rows) + r"\end{array}"


def _inter_tex(parts: list[Type], system: System, style: Style) -> str:
    """An intersection with at least one component, as a domain or a context entry."""
    if system.idempotent:
        if len(parts) == 1:
            return type_tex(parts[0], system, style)
        items = [_inter_part(p, system, style) for p in parts]
        if style.stacked:
            return _stack([f"{x} \\cap" for x in items[:-1]] + [items[-1]])
        return r" \cap ".join(items)
    items = [type_tex(p, system, style) for p in parts]
    if style.stacked and len(parts) > 1:
        return r"\left[" + _stack([f"{x}," for x in items[:-1]] + [items[-1]]) + r"\right]"
    return "[" + ", ".join(items) + "]"


def type_tex(t: Type, system: System, style: Style = PLAIN) -> str:
    for ty, name in style.abbrevs:
        if ty == t:
            return name
    match t:
        case Atom(name):
            return dict(style.atoms).get(name) or atom_tex(name)
        case Inter(()):
            return r"\omega" if system.idempotent else r"[\,]"
        case Inter(parts):
            return _inter_tex(list(parts), system, style)
        case Arrow(dom, cod):
            if system.idempotent:
                d = type_tex(dom, system, style)
                if not _abbreviated(dom, style) and (isinstance(dom, Arrow) or (isinstance(dom, Inter) and dom.parts)):
                    d = rf"\left({d}\right)" if style.stacked and isinstance(dom, Inter) else f"({d})"
            else:
                d = type_tex(dom, system, style) if isinstance(dom, Inter) else _inter_tex([dom], system, style)
            return rf"{d} \to {type_tex(cod, system, style)}"
    raise TypeError(t)


def _abbreviated(t: Type, style: Style) -> bool:
    return any(ty == t for ty, _ in style.abbrevs)


def _inter_part(t: Type, system: System, style: Style = PLAIN) -> str:
    s = type_tex(t, system, style)
    return f"({s})" if isinstance(t, Arrow) and not _abbreviated(t, style) else s


def context_tex(c: Context, system: System, style: Style = PLAIN) -> str:
    return ", ".join(f"{name_tex(x)} : {_inter_tex(ts, system, style)}" for x, ts in sorted(c.items()))


def judgement_tex(d: Deriv, system: System, style: Style = PLAIN) -> str:
    ctx = context_tex(context(d, system), system, style)
    return rf"{ctx} \vdash {term_tex(d.term)} : {type_tex(d.type, system, style)}"


DEFAULT_WIDTH = 150  # estimated characters of \\small math that fit a landscape A4 line
_GAP = 4  # space between premises, in characters


_ARRAY = re.compile(r"\\begin\{array\}\[c\]\{@\{\}l@\{\}\}((?:(?!\\begin\{array\}).)*?)\\end\{array\}", re.S)


def tex_width(tex: str) -> float:
    """A rough estimate of the printed width of math `tex`, in characters.
    A stacked array counts as wide as its widest row."""
    while m := _ARRAY.search(tex):
        rows = m.group(1).split(r" \\ ")
        tex = tex[: m.start()] + "x" * round(max(tex_width(r) for r in rows)) + tex[m.end():]
    tex = tex.replace(r"\left", "").replace(r"\right", "")
    tex = tex.replace(r"\,", "").replace(r"\quad", "  ")
    tex = re.sub(r"_\{([^{}]*)\}", lambda m: "x" * round(0.7 * len(m.group(1))), tex)
    tex = re.sub(r"\\(mathit|mathrm|textsf|textbf|underline)\{", "{", tex)
    tex = re.sub(r"\\(to|vdash|cap)\b", "xx", tex)
    tex = re.sub(r"\\[A-Za-z]+", "x", tex)
    return len(tex.replace("{", "").replace("}", "").replace("$", ""))


def label_tex(k: int) -> str:
    return rf"\textsf{{tree{k}}}"


_LABEL_WIDTH = 6


@dataclass(eq=False)
class _Node:
    """A derivation laid out for printing. A premise is a node printed in place, or a
    group of nodes printed elsewhere (labelled) and referred to by their labels."""

    deriv: Deriv
    judgement: str
    premises: list["_Node | list[_Node]"]
    width: float


def fitted_judgement(d: Deriv, system: System, style: Style, width: float) -> str:
    """The judgement in `style`, with stacked intersections if it does not fit otherwise."""
    j = judgement_tex(d, system, style)
    if tex_width(j) > width and not style.stacked:
        return judgement_tex(d, system, style.with_(stacked=True))
    return j


def _layout(d: Deriv, system: System, width: float, style: Style = PLAIN, judge=None) -> _Node:
    """Bottom-up: when the premises of a rule do not fit side by side in `width`, the
    widest one is moved out under a label; more than five premises share one.
    `judge`, if given, renders a judgement instead of fitted_judgement."""
    premises: list[_Node | list[_Node]] = [_layout(p, system, width, style, judge) for p in d.premises]
    if len(premises) > MAX_PREMISES:
        premises = premises[: MAX_PREMISES - 1] + [list(premises[MAX_PREMISES - 1:])]

    def w(p: _Node | list[_Node]) -> float:
        return p.width if isinstance(p, _Node) else len(p) * _LABEL_WIDTH + _GAP * (len(p) - 1)

    # With a single premise moving it out cannot help: it is only wider than `width`
    # when its own judgement is.
    while len(premises) > 1 and sum(w(p) for p in premises) + _GAP * (len(premises) - 1) > width:
        inline = [i for i, p in enumerate(premises) if isinstance(p, _Node)]
        if not inline:
            break
        i = max(inline, key=lambda i: premises[i].width)
        premises[i] = [premises[i]]
    j = judge(d) if judge else fitted_judgement(d, system, style, width)
    above = sum(w(p) for p in premises) + _GAP * max(len(premises) - 1, 0)
    return _Node(d, j, premises, max(tex_width(j), above))


def derivation_trees(d: Deriv, system: System, width: float = DEFAULT_WIDTH, style: Style = PLAIN,
                     judge=None, rule_names: dict[str, str] | None = None) -> list[str]:
    """The derivation as bussproofs trees (each ending in \\DisplayProof): the main tree
    first, then the trees for the labels tree1, tree2, ..., numbered in reading order."""
    infer = {1: "UnaryInfC", 2: "BinaryInfC", 3: "TrinaryInfC", 4: "QuaternaryInfC", 5: "QuinaryInfC"}
    queue: list[_Node] = [_layout(d, system, width, style, judge)]

    def render(node: _Node, lines: list[str]) -> None:
        for p in node.premises:
            if isinstance(p, _Node):
                render(p, lines)
            else:
                labels = []
                for sub in p:
                    queue.append(sub)
                    labels.append(label_tex(len(queue) - 1))
                lines.append(rf"\AxiomC{{${r' \quad '.join(labels)}$}}")
        if not node.premises:
            lines.append(r"\AxiomC{}")
        rule = (rule_names or {}).get(node.deriv.rule, node.deriv.rule)
        lines.append(rf"\RightLabel{{\scriptsize {rule}}}")
        lines.append(rf"\{infer[len(node.premises) or 1]}{{${node.judgement}$}}")

    trees = []
    i = 0
    while i < len(queue):  # rendering a tree may queue more labelled trees
        lines: list[str] = []
        render(queue[i], lines)
        trees.append("\n".join(lines) + "\n\\DisplayProof")
        i += 1
    return trees


def derivation_tex(d: Deriv, system: System, width: float = DEFAULT_WIDTH, style: Style = PLAIN,
                   judge=None, rule_names: dict[str, str] | None = None) -> str:
    """All trees of the derivation, each in \\small and centred, labelled trees after the main one."""
    trees = derivation_trees(d, system, width, style, judge, rule_names)
    parts = [r"\begin{center}\small" + "\n" + trees[0] + "\n\\end{center}"]
    for k, tree in enumerate(trees[1:], start=1):
        parts.append(rf"\noindent ${label_tex(k)}$:" + "\n" + r"\begin{center}\small" + "\n" + tree + "\n\\end{center}")
    return "\n\n".join(parts)


PREAMBLE = r"""\documentclass[a4paper,landscape]{article}
\usepackage[margin=1.5cm]{geometry}
\usepackage{amsmath,amssymb}
\usepackage{bussproofs}
\usepackage{xcolor}
\setlength{\parindent}{0pt}
\begin{document}
"""


def document(body: str) -> str:
    return PREAMBLE + body + "\n\\end{document}\n"


def source_tex(statements: list[Statement], system: System) -> str:
    """The input file as written (before substituting definitions), in lambda notation."""
    rows = []
    for st in statements:
        match st:
            case TypeDecl(var, ty, _):
                rows.append(rf"{name_tex(var)} &: {type_tex(ty, system)}")
            case Def(name, t, _):
                rows.append(rf"{name_tex(name)} &= {term_tex(t)}")
            case Canonical(t, _, _):
                rows.append(rf"&\textbf{{canonical: }} {term_tex(t)}")
    if not rows:
        return ""
    return "\\section*{Source}\n\\begin{align*}\n" + " \\\\\n".join(rows) + "\n\\end{align*}\n"


def reduction_tex(name: str, source: Term, terms: tuple[Term, ...], redexes: tuple[Position, ...], strategy: str, mark: bool) -> str:
    n = len(redexes)
    items = []
    for i, t in enumerate(terms):
        m = redexes[i] if mark and i < n else None
        items.append(rf"  \item[{i}:] ${term_tex(t, m)}$")
    head = rf"\section*{{${name_tex(name)} = {term_tex(source)}$ \quad \normalsize({strategy}, {n} step{'s' if n != 1 else ''})}}"
    return head + "\n\\begin{description}\n" + "\n".join(items) + "\n\\end{description}\n"


def _subderivations(d: Deriv) -> list[Deriv]:
    out, todo = [], [d]
    while todo:
        x = todo.pop()
        out.append(x)
        todo.extend(reversed(x.premises))
    return out


def _atoms_in_order(ds: list[Deriv], system: System) -> list[str]:
    seen: dict[str, None] = {}

    def walk(t: Type) -> None:
        match t:
            case Atom(name):
                seen.setdefault(name)
            case Arrow(dom, cod):
                walk(dom)
                walk(cod)
            case Inter(parts):
                for p in parts:
                    walk(p)

    for x in ds:
        for ts in context(x, system).values():
            for t in ts:
                walk(t)
        walk(x.type)
    return list(seen)


def _arrow_subtypes(t: Type) -> list[Type]:
    match t:
        case Arrow(dom, cod):
            return [t, *_arrow_subtypes(dom), *_arrow_subtypes(cod)]
        case Inter(parts):
            return [s for p in parts for s in _arrow_subtypes(p)]
    return []


def plan_style(d: Deriv, system: System, width: float = DEFAULT_WIDTH) -> Style:
    """The plainest style in which every judgement of d fits `width`:

    1. the standard notation (a judgement that does not fit gets stacked intersections,
       see fitted_judgement);
    2. if some judgement still does not fit, atoms of the whole derivation are renamed
       to \alpha_1, \alpha_2, ... in order of appearance;
    3. if some still does not fit, the widest arrow types of the widest judgement are
       named \tau_1, \tau_2, ... until everything fits (or nothing is left to name).
    """
    ds = _subderivations(d)

    def too_wide(style: Style) -> list[Deriv]:
        return [x for x in ds if tex_width(fitted_judgement(x, system, style, width)) > width]

    style = PLAIN
    if not too_wide(style):
        return style
    generated = [a for a in _atoms_in_order(ds, system) if _GENERATED_ATOM.match(a)]
    style = Style(atoms=tuple((a, rf"\alpha_{{{k}}}") for k, a in enumerate(generated, start=1)))
    while bad := too_wide(style):
        worst = max(bad, key=lambda x: tex_width(fitted_judgement(x, system, style, width)))
        types = [t for ts in context(worst, system).values() for t in ts] + [worst.type]
        candidates = [
            t for ty in types for t in _arrow_subtypes(ty)
            if not _abbreviated(t, style) and tex_width(type_tex(t, system, style)) > 8
        ]
        if not candidates:
            break
        best = max(candidates, key=lambda t: tex_width(type_tex(t, system, style)))
        style = style.with_(abbrevs=style.abbrevs + ((best, rf"\tau_{{{len(style.abbrevs) + 1}}}"),))
    return style


def legend_tex(style: Style, system: System) -> str:
    """Definitions of the type abbreviations and short atom names of `style`."""
    parts = []
    if style.abbrevs:
        rows = []
        for ty, name in style.abbrevs:
            others = style.with_(abbrevs=tuple((t, n) for t, n in style.abbrevs if n != name), stacked=False)
            rows.append(rf"{name} &= {type_tex(ty, system, others)}")
        parts.append("\\begin{align*}\n" + " \\\\\n".join(rows) + "\n\\end{align*}")
    if style.atoms:
        parts.append(r"\[ " + r",\quad ".join(f"{short} = {atom_tex(a)}" for a, short in style.atoms) + r" \]")
    if not parts:
        return ""
    return "\\noindent where\n" + "\n".join(parts)


def derivation_section(title: str, d: Deriv, system: System, width: float = DEFAULT_WIDTH) -> str:
    style = plan_style(d, system, width)
    parts = [
        rf"\subsection*{{{title}}}",
        rf"\[ {fitted_judgement(d, system, style, width)} \]",
        derivation_tex(d, system, width, style),
    ]
    legend = legend_tex(style, system)
    if legend:
        parts.append(legend)
    return "\n\n".join(parts) + "\n"


# --- SIAM runs -------------------------------------------------------------------------

SIAM_RULES = {"abs": r"T-$\lambda$", "app": "T-@", "var": "T-Var", "lamstar": r"T-$\lambda_\star$"}


def seq_type_tex(t: Type, ann: dict | None = None, prefix: tuple = ()) -> str:
    """A sequence type, the ★ at annotated paths with their visits (red up, blue down)."""
    from .siam import seq

    ann = ann or {}
    match t:
        case Atom():
            visits = ann.get(prefix)
            if not visits:
                return r"\star"
            marks = ",".join(
                (r"\textcolor{red}{\uparrow" if v[0] == "↑" else r"\textcolor{blue}{\downarrow") + v[1:] + "}"
                for v in visits.split(",")
            )
            return rf"\star_{{{marks}}}"
        case Arrow(dom, cod):
            items = [seq_type_tex(a, ann, prefix + (("dom", i),)) for i, a in enumerate(seq(dom))]
            return rf"[{', '.join(items)}] \to {seq_type_tex(cod, ann, prefix + (('cod',),))}"
    raise TypeError(t)


def siam_section(title: str, r, summary: str, width: float = DEFAULT_WIDTH) -> str:
    """A SIAM run: the sequence derivation with every ★ on the right of \\vdash numbered."""
    from .siam import annotations, seq_context

    ann = annotations(r)
    ids = {id(d): n for n, d in enumerate(r.index.nodes)}

    def judge(d: Deriv) -> str:
        ctx = ", ".join(
            f"{name_tex(x)} : [{', '.join(seq_type_tex(t) for t in ts)}]" for x, ts in sorted(seq_context(d).items())
        )
        return rf"{ctx} \vdash {term_tex(d.term)} : {seq_type_tex(d.type, ann.get(ids[id(d)]))}"

    system = None  # not used when `judge` is given
    return "\n\n".join([
        rf"\subsection*{{{title}}}",
        summary,
        derivation_tex(r.derivation, system, width, PLAIN, judge, SIAM_RULES),
    ]) + "\n"
