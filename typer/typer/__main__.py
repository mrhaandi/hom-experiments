"""Command line: python -m typer FILE [options]."""

import argparse
import contextlib
import sys

from .addresses import addresses, show_address
from .derive import Deriv, Expander, canonical, check, fit_declarations
from .display import judgement, show_derivation
from . import siam
from . import latex
from .evaluate import Evaluated, evaluate
from .parser import TyperError, parse_file
from .reduce import DEFAULT_MAX_STEPS, STRATEGIES
from .systems import DEFAULT_SYSTEM, SYSTEMS, get_system
from .terms import show_term


def print_parsed(prog) -> None:
    for var, ty in prog.env.items():
        print(f"{var} : {ty}")
    for name, t in prog.defs.items():
        print(f"{name} = {t}")
    for c in prog.commands:
        print(f"cannonical: {c.source}  =  {c.term}")


def print_addresses(ev: Evaluated) -> None:
    for c, t in ev.canonical:
        print(f"cannonical: {c.source} = {show_term(t)}")
        table = addresses(t)
        width = max(len(show_address(a)) for a, _ in table)
        for a, sub in table:
            print(f"  {show_address(a):<{width}}  {show_term(sub)}")
        print()


def source_of(ev: Evaluated, name: str):
    return next(s for s in ev.program.statements if getattr(s, "name", None) == name)


def print_reduction(ev: Evaluated, name: str, mark_redex: bool) -> None:
    trace = ev.traces[name]
    n = trace.steps
    print(f"{name} = {show_term(source_of(ev, name).term)}    [{trace.strategy}, {n} step{'s' if n != 1 else ''}]")
    width = len(str(n))
    for i, t in enumerate(trace.terms):
        mark = trace.redexes[i] if mark_redex and i < n else None
        print(f"  {i:>{width}}: {show_term(t, mark)}")
    print()


def print_reductions(ev: Evaluated, mark_redex: bool) -> None:
    for name in ev.traces:
        print_reduction(ev, name, mark_redex)
    for c, t in ev.canonical:
        print(f"cannonical: {c.source} = {show_term(t)}")


# name -> terms whose derivation was obtained along normal order (see Expander.along)
RESTARTS: dict[str, list[int]] = {}


def derivations(ev: Evaluated, name: str, fit: bool = False) -> list[Deriv]:
    """Derivations of the numbered terms of `name`: canonical for the normal form, expanded before it."""
    declarations = ev.program.env if fit else None
    if name in ev.traces:
        expander = Expander(ev.system, ev.strategy, ev.max_steps)
        ds = expander.along(ev.traces[name], declarations)
        RESTARTS[name] = expander.restarts
    elif name in ev.defs:
        ds = [canonical(ev.defs[name], ev.system)]
        if declarations:
            ds = [fit_declarations(ds[0], declarations, ev.system)]
    else:
        raise TyperError(f"--show: {name!r} is not defined")
    for d in ds:
        check(d, ev.system)
    return ds


def parse_show(spec: str) -> tuple[str, list[int] | None]:
    name, _, idx = spec.partition(":")
    if not idx or idx == "all":
        return name, None
    try:
        return name, [int(i) for i in idx.split(",")]
    except ValueError:
        raise TyperError(f"--show {spec}: expected NAME, NAME:all or NAME:i,j,...") from None


def selected_derivations(ev: Evaluated, specs: list[str], fit: bool):
    """(name, index, kind, derivation) for every derivation asked for with --show."""
    for spec in specs:
        name, idx = parse_show(spec)
        ds = derivations(ev, name, fit)
        for i in idx if idx is not None else range(len(ds)):
            if not 0 <= i < len(ds):
                raise TyperError(f"--show {spec}: {name} has terms 0..{len(ds) - 1}")
            if i == len(ds) - 1:
                kind = "canonical"
            elif i in RESTARTS.get(name, []):
                kind = "expanded along cbn"
            else:
                kind = "expanded"
            yield name, i, kind, ds[i]


def print_derivations(ev: Evaluated, specs: list[str], fit: bool, mark_redex: bool) -> None:
    """Derivations, each group preceded by the reduction of its term."""
    shown: set[str] = set()
    for name, i, kind, d in selected_derivations(ev, specs, fit):
        if name not in shown and name in ev.traces:
            print_reduction(ev, name, mark_redex)
        shown.add(name)
        print(f"{name} [{i}] ({kind}, {ev.system}, {ev.strategy}):")
        print(f"  {judgement(d, ev.system)}")
        print(show_derivation(d, ev.system, indent="    "))
        print()


def siam_runs(ev: Evaluated, specs: list[str], any_type: bool):
    """(name, index, run) for every term asked for with --siam."""
    for spec in specs:
        name, idx = parse_show(spec)
        if name in ev.traces:
            terms = ev.traces[name].terms
        elif name in ev.defs:
            terms = (ev.defs[name],)
        else:
            raise TyperError(f"--siam: {name!r} is not defined")
        for i in idx if idx is not None else range(len(terms)):
            if not 0 <= i < len(terms):
                raise TyperError(f"--siam {spec}: {name} has terms 0..{len(terms) - 1}")
            d, _ = siam.weak_head_derivation(terms[i])
            yield name, i, siam.run(d, any_type)


def print_siam(ev: Evaluated, specs: list[str], any_type: bool) -> None:
    for name, i, r in siam_runs(ev, specs, any_type):
        print(f"{name} [{i}] (SIAM): {siam.summary(r)}")
        print(siam.show_run(r))
        print()


def latex_document(ev: Evaluated, specs: list[str], fit: bool, mark_redex: bool,
                   width: float = latex.DEFAULT_WIDTH, siam_specs: list[str] | None = None,
                   any_type: bool = False) -> str:
    """The source, then with --show the chosen derivations, each group after its reduction;
    otherwise the numbered reductions."""
    def reduction(name: str) -> str:
        trace = ev.traces[name]
        return latex.reduction_tex(name, source_of(ev, name).term, trace.terms, trace.redexes, trace.strategy, mark_redex)

    body = []
    if siam_specs:
        for name, i, r in siam_runs(ev, siam_specs, any_type):
            title = rf"${latex.name_tex(name)}$ [{i}] \quad \normalsize(SIAM)"
            body.append(latex.siam_section(title, r, siam.summary(r, latex=True), width))
        return latex.document("\n".join([latex.source_tex(ev.program.statements, ev.system), *body]))
    if specs:
        shown: set[str] = set()
        for name, i, kind, d in selected_derivations(ev, specs, fit):
            if name not in shown and name in ev.traces:
                body.append(reduction(name))
            shown.add(name)
            title = rf"${latex.name_tex(name)}$ [{i}] \quad \normalsize({kind}, {ev.system}, {ev.strategy})"
            body.append(latex.derivation_section(title, d, ev.system, width))
    else:
        body = [reduction(name) for name in ev.traces]
    source = latex.source_tex(ev.program.statements, ev.system)
    return latex.document("\n".join([source, *body]))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(prog="typer", description="Typing examples in intersection type systems.")
    ap.add_argument("file", help="input file")
    ap.add_argument("--parse", action="store_true", help="only parse the file and print what was read")
    ap.add_argument("--system", choices=list(SYSTEMS), default=DEFAULT_SYSTEM,
                    help=f"type system (default: {DEFAULT_SYSTEM})")
    ap.add_argument("--strategy", choices=STRATEGIES, default="cbn",
                    help="cbn = normal order, cbv = applicative order (default: cbn)")
    ap.add_argument("--max-steps", type=int, default=DEFAULT_MAX_STEPS,
                    help=f"give up a reduction after this many steps (default: {DEFAULT_MAX_STEPS})")
    ap.add_argument("--addresses", action="store_true", help="list the addresses of subterms of cannonical terms")
    ap.add_argument("--show", action="append", default=[], metavar="NAME[:i,j,...]",
                    help="print derivations of the numbered terms of NAME (all if no numbers); may be repeated")
    ap.add_argument("--siam", action="append", default=[], metavar="NAME[:i,j,...]",
                    help="run the Sequence IAM on the numbered terms of NAME and show the sequence "
                         "derivation with each occurrence of the star numbered by its visit")
    ap.add_argument("--siam-any-type", action="store_true",
                    help="--siam: start on the rightmost star of any final type, not only on a closed term of type star")
    ap.add_argument("--fit-declarations", action="store_true",
                    help="instantiate the canonical typing so that free variables get their declared types")
    ap.add_argument("--format", choices=["text", "latex"], default="text",
                    help="latex: a complete document (bussproofs) with the derivations of --show, "
                         "or with the reductions when --show is not given")
    ap.add_argument("--width", type=float, default=latex.DEFAULT_WIDTH,
                    help="LaTeX: estimated line width in characters; wider subtrees are printed separately "
                         f"under labels tree1, tree2, ... (default: {latex.DEFAULT_WIDTH})")
    ap.add_argument("-o", "--output", metavar="FILE", help="write the output to FILE instead of the screen")
    ap.add_argument("--mark-redex", action="store_true", help="show the contracted redex of each step in [ ]")
    args = ap.parse_args(argv)

    try:
        prog = parse_file(args.file)
        if args.parse:
            print_parsed(prog)
            return 0
        ev = evaluate(prog, get_system(args.system), args.strategy, args.max_steps)
        out = open(args.output, "w", encoding="utf-8") if args.output else None
        with contextlib.redirect_stdout(out) if out else contextlib.nullcontext():
            if args.format == "latex":
                print(latex_document(ev, args.show, args.fit_declarations, args.mark_redex, args.width,
                                     args.siam, args.siam_any_type), end="")
            elif args.siam:
                print_siam(ev, args.siam, args.siam_any_type)
            elif args.show:
                print_derivations(ev, args.show, args.fit_declarations, args.mark_redex)
            elif args.addresses:
                print_addresses(ev)
            else:
                print_reductions(ev, args.mark_redex)
        if out:
            out.close()
    except TyperError as e:
        print(f"{args.file}: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
