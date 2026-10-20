# typer

Typing examples in intersection type systems (idempotent / non-idempotent, with / without omega).

Run from this folder (Python 3.10+, no dependencies):

    python3 -m typer examples/basic.txt --parse      # what was read
    python3 -m typer examples/reductions.txt              # numbered reductions
    python3 -m typer examples/normal_form.txt --mark-redex
    python3 -m typer examples/reductions.txt --strategy cbv --mark-redex
    python3 -m unittest -v                              # tests are in tests/

Options:

- `--system idem|idem-omega|nonidem|nonidem-omega` (default `idem`). All four use strict types:
  intersections and omega only as an arrow domain or as the whole type of a variable.
  Idempotent: `a /\ a = a`; non-idempotent: intersections are multisets.
- `--strategy cbn|cbv` (default `cbn`): normal order or applicative order; both reduce
  under `fun` and go to the full beta-normal form.
- `--max-steps N` (default 1000): a reduction longer than this is reported as an error.
- `--mark-redex`: shows the contracted redex of each step in `[ ]`.

## Input format

One statement per line, `#` starts a comment.

    v : a /\ (a -> a)            # type declaration of a term variable
    M = fun x.fun y.x y          # term definition
    N = fun x y. a x y           # `fun x y.` = `fun x.fun y.`
    M1 = (fun x.x)(fun y.y)
    M2 = NF(M1)                  # beta-normal form
    cannonical: M2               # canonical derivation of a normal form (`canonical:` also works)

- Terms: `fun` (or `\`, `λ`) binds as far right as possible; application associates to the left.
- Names defined with `=` are substituted without variable capture; every other name is a variable.
  A defined name must be defined before it is used; a bound variable shadows a defined name.
- Types: `/\` (or `∧`) binds tighter than `->` (or `→`), which associates to the right;
  `omega` (or `ω`) is the empty intersection. Type names and term names are independent.

## Subterm addresses (normal forms)

The root is `ε` (also `eps` in input). If the subterm at `p` is `y M1 ... Mk`, then `p,0` is `y` and `p,i` is `Mi`.
If it is `fun x0 ... xk. M`, then `p,0^j` strips the first `j` binders and `p,0^(k+1)` is `M`.
`python3 -m typer examples/addresses.txt --addresses` lists all addresses of each `cannonical:` term.

## Derivations

    python3 -m typer examples/normal_form.txt --show M2          # all numbered terms of M2
    python3 -m typer examples/normal_form.txt --show M2:0,7      # only terms 0 and 7
    python3 -m typer examples/normal_form.txt --show M2 --system nonidem-omega --strategy cbv

With `--show` (text or LaTeX) the derivations of a name are preceded by its numbered reduction
(with `--mark-redex`, the contracted redexes are marked there).

The last term of a reduction (the normal form) gets its canonical derivation: the application
`y M1 ... Mk` at address `p` has the atom `a_{p}` and `y` gets `T1 -> ... -> Tk -> a_{p}`;
an abstraction collects the types of its variable (omega if unused, or, without omega, the atom
`a_{p}` of its own address). Every earlier term gets a derivation by subject expansion, one
redex at a time, and every derivation is verified by an independent checker.

## LaTeX

    python3 -m typer examples/normal_form.txt --format latex --mark-redex -o reduction.tex
    python3 -m typer examples/normal_form.txt --format latex --show M2:0,7 -o derivations.tex

`--format latex` writes a complete document (packages: amsmath, amssymb, bussproofs, geometry). It starts with the source file in lambda notation (definitions as written, `M2` as
`M_{2}`), followed, with `--show`, by the chosen derivations, otherwise the numbered reductions (redexes
underlined with `--mark-redex`). Idempotent systems are written with `\cap` and `\omega`,
non-idempotent ones with multisets `[A, B] \to C` and `[\,]`. Trees are typeset in `\small` and never scaled. When the premises of a rule would not fit side
by side in the line (estimated as `--width` characters, default 150 for landscape A4), the widest
one is replaced by a label `tree1`, `tree2`, ... and printed below as its own tree; labels are
numbered in reading order. A rule with more than five premises (the bussproofs limit) gets its
last ones as labels too. When a single judgement is wider than the line, it is shortened in steps: first its
intersections are written one below the other (`a \cap` above `b`); if some judgement of the
derivation still does not fit, all generated atoms of that derivation are renamed `\alpha_1,
\alpha_2, ...`; if still needed, the widest arrow types are named `\tau_1, \tau_2, ...`. The
definitions of `\alpha_i` and `\tau_i` are printed below the derivation.
Sample outputs are in `examples/latex/`.

`--fit-declarations` instantiates the atoms `a_{...}` of the canonical derivation so that every
declared free variable (`v : T` in the file) is used exactly with the components of `T` (as a
multiset in non-idempotent systems, as a set in idempotent ones), and reports an error if that is
impossible. Without the flag declarations are ignored. See `examples/declarations.txt`.

Rules: `var`, `abs`, `app` with strict types. In non-idempotent systems an argument has exactly
one derivation per component of the domain; in idempotent ones it may have several with the
same type (copies of a duplicated argument) as long as their types are exactly the domain.

With omega the type and the context are preserved by expansion. Without omega an erased argument
is typed through its own normal form (atoms `b_{...}`, `c_{...}`, ...), so free variables of it
enter the context, and the domain of a binder above the redex may grow. One case is not supported
yet and is reported as an error: without omega, under cbv, when that growth would change the domain
of an abstraction that is already applied to an argument.

## Sequence types and the SIAM

    python3 -m typer examples/siam.txt --siam M
    python3 -m typer examples/siam.txt --siam M --format latex -o siam.tex

`--siam NAME[:i,j,...]` converts the numbered terms of NAME to sequence types and runs the
Sequence IAM of Accattoli, Dal Lago and Vanoni ("The (In)Efficiency of Interaction", sections
12-13). Sequence types are the non-idempotent types with multisets replaced by sequences and
every atom by the star; the derivation is the one of the paper: T-λ★ for the weak head normal
form, expanded back along the weak head reduction, so the term must be closed. The machine
starts on the conclusion going up, and every occurrence of the star on the right of a turnstile
is annotated with the step that visits it and its direction (up/down), so the run can be read
off the derivation. `--siam-any-type` starts on the rightmost star of any final type instead.

The run visits every occurrence of the star exactly once, so its length is the λIAM weight
W_λIAM of the derivation; the printed summary says so, and the tests check it.

## Status

1. Input parser: done.
2. Core, the four systems, cbn/cbv reduction: done.
3. Canonical derivations, subject expansion, checker: done (plain-text output).
4. Text/LaTeX output: done.
5. Conversion to sequence types and the SIAM: done.
