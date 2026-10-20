"""Parser for typer input files.

One statement per line; `#` starts a comment.

    v : a /\\ (a -> a)            type declaration of a term variable
    M = fun x.fun y.x y          term definition
    N = fun x y. a x y           `fun x y.` abbreviates `fun x.fun y.`
    M2 = NF(M1)                  beta-normal form of a term
    cannonical: M2               canonical derivation of a normal form

Terms: `fun` (also `\\` or `λ`) binds as far right as possible, application
associates to the left. Names defined with `=` are substituted (without
capture); any other name is a variable. Types: `/\\` (or `∧`) binds tighter
than `->` (or `→`), which associates to the right; `omega` (or `ω`) is the
empty intersection.
"""

from __future__ import annotations

import re
from dataclasses import dataclass, field

from .itypes import OMEGA, Arrow, Atom, Type, inter
from .terms import NF, App, Lam, Term, Var, free_vars, subst


class TyperError(Exception):
    def __init__(self, msg: str, line: int | None = None, col: int | None = None):
        self.msg, self.line, self.col = msg, line, col
        where = "" if line is None else f"line {line}" + ("" if col is None else f", col {col}") + ": "
        super().__init__(where + msg)


# --- statements --------------------------------------------------------------


@dataclass(frozen=True)
class TypeDecl:
    var: str
    type: Type
    line: int


@dataclass(frozen=True)
class Def:
    name: str
    term: Term
    line: int


@dataclass(frozen=True)
class Canonical:
    term: Term
    source: str  # the argument as written, e.g. "M2"
    line: int


Statement = TypeDecl | Def | Canonical

CANONICAL_KEYWORDS = {"cannonical", "canonical"}


# --- lexer -------------------------------------------------------------------

_TOKEN_RE = re.compile(
    r"""
    (?P<ws>[ \t\n]+)
  | (?P<arrow>->|→)
  | (?P<inter>/\\|∧)
  | (?P<lam>\\|λ)
  | (?P<ident>[A-Za-z_][A-Za-z0-9_']*)
  | (?P<omega>ω)
  | (?P<punct>[().=:])
    """,
    re.VERBOSE,
)


@dataclass
class Tok:
    kind: str  # ident, arrow, inter, lam, omega, punct, eof
    text: str
    col: int
    line: int = 0


def tokenize(text: str, line: int) -> list[Tok]:
    """`text` may span several lines; `line` is the number of its first line."""

    def where(pos: int) -> tuple[int, int]:
        return line + text.count("\n", 0, pos), pos - (text.rfind("\n", 0, pos) + 1) + 1

    toks, pos = [], 0
    while pos < len(text):
        m = _TOKEN_RE.match(text, pos)
        if not m:
            raise TyperError(f"unexpected character {text[pos]!r}", *where(pos))
        kind = m.lastgroup
        if kind != "ws":
            ln, col = where(pos)
            tok = Tok(kind, m.group(), col, ln)
            if kind == "ident" and tok.text == "fun":
                tok.kind = "lam"
            elif kind == "ident" and tok.text == "omega":
                tok.kind = "omega"
            toks.append(tok)
        pos = m.end()
    toks.append(Tok("eof", "", *reversed(where(len(text)))))
    return toks


class _Parser:
    def __init__(self, text: str, line: int):
        self.toks = tokenize(text, line)
        self.i = 0
        self.line = line

    @property
    def peek(self) -> Tok:
        return self.toks[self.i]

    def next(self) -> Tok:
        tok = self.toks[self.i]
        self.i += 1
        return tok

    def error(self, msg: str, tok: Tok | None = None) -> TyperError:
        tok = tok or self.peek
        found = "end of the statement" if tok.kind == "eof" else repr(tok.text)
        return TyperError(f"{msg}, found {found}", tok.line, tok.col)

    def expect(self, text: str) -> Tok:
        if self.peek.text != text or self.peek.kind not in ("punct", "lam"):
            raise self.error(f"expected {text!r}")
        return self.next()

    def ident(self) -> str:
        if self.peek.kind != "ident":
            raise self.error("expected a name")
        return self.next().text

    def end(self) -> None:
        if self.peek.kind != "eof":
            raise self.error("unexpected input")

    # terms

    def term(self) -> Term:
        if self.peek.kind == "lam":
            self.next()
            vars_ = [self.ident()]
            while self.peek.kind == "ident":
                vars_.append(self.ident())
            self.expect(".")
            body = self.term()
            for v in reversed(vars_):
                body = Lam(v, body)
            return body
        t = self.atom()
        while True:
            if self.peek.kind == "lam":  # a trailing abstraction is the last argument
                return App(t, self.term())
            if self.peek.kind == "ident" or self.peek.text == "(":
                t = App(t, self.atom())
            else:
                return t

    def atom(self) -> Term:
        tok = self.peek
        if tok.kind == "ident" and tok.text == "NF":
            self.next()
            self.expect("(")
            t = self.term()
            self.expect(")")
            return NF(t)
        if tok.kind == "ident":
            return Var(self.next().text)
        if tok.text == "(":
            self.next()
            t = self.term()
            self.expect(")")
            return t
        raise self.error("expected a term")

    # types

    def type(self) -> Type:
        dom = self.inter_type()
        if self.peek.kind == "arrow":
            self.next()
            return Arrow(dom, self.type())
        return dom

    def inter_type(self) -> Type:
        parts = [self.type_atom()]
        while self.peek.kind == "inter":
            self.next()
            parts.append(self.type_atom())
        return inter(parts)

    def type_atom(self) -> Type:
        tok = self.peek
        if tok.kind == "omega":
            self.next()
            return OMEGA
        if tok.kind == "ident":
            return Atom(self.next().text)
        if tok.text == "(":
            self.next()
            t = self.type()
            self.expect(")")
            return t
        raise self.error("expected a type")


def parse_type(text: str, line: int = 1) -> Type:
    p = _Parser(text, line)
    t = p.type()
    p.end()
    return t


def parse_term(text: str, line: int = 1) -> Term:
    p = _Parser(text, line)
    t = p.term()
    p.end()
    return t


def parse_statement(text: str, line: int) -> Statement:
    p = _Parser(text, line)
    tok = p.peek
    if tok.kind != "ident":
        raise p.error("expected a declaration, a definition or a command")
    name = p.next().text
    if p.peek.text == ":" and name in CANONICAL_KEYWORDS:
        p.next()
        start = p.peek.col - 1
        t = p.term()
        p.end()
        return Canonical(t, text[start:].strip(), line)
    if p.peek.text == ":":
        p.next()
        ty = p.type()
        p.end()
        return TypeDecl(name, ty, line)
    if p.peek.text == "=":
        p.next()
        t = p.term()
        p.end()
        return Def(name, t, line)
    raise p.error(f"expected ':' or '=' after {name!r}")


# --- programs ----------------------------------------------------------------


@dataclass
class Program:
    """A parsed input file with defined names substituted.

    `defs` and `commands` hold resolved terms: they contain no defined names,
    but may still contain NF(...) markers, which evaluation replaces.
    """

    statements: list[Statement] = field(default_factory=list)
    env: dict[str, Type] = field(default_factory=dict)
    defs: dict[str, Term] = field(default_factory=dict)
    commands: list[Canonical] = field(default_factory=list)


def _strip_comment(line: str) -> str:
    i = line.find("#")
    return line if i < 0 else line[:i]


_STATEMENT_START = re.compile(r"^[A-Za-z_][A-Za-z0-9_']*\s*[:=]")


def statement_blocks(text: str) -> list[tuple[int, str]]:
    """Splits a file into statements: (number of the first line, text).

    A statement may span several lines. It ends at a blank line, or where a
    line that is not indented starts a new statement (`name :`, `name =`,
    `cannonical:`), so consecutive one-line statements need no blank lines.
    """
    blocks: list[tuple[int, list[str]]] = []
    current: tuple[int, list[str]] | None = None
    for n, raw in enumerate(text.splitlines(), start=1):
        line = _strip_comment(raw).rstrip()
        if not line.strip():
            current = None
            continue
        starts = not line[0].isspace() and _STATEMENT_START.match(line)
        if current is None or starts:
            current = (n, [])
            blocks.append(current)
        current[1].append(line)
    return [(n, "\n".join(lines)) for n, lines in blocks]


def parse_program(text: str) -> Program:
    return resolve([parse_statement(t, n) for n, t in statement_blocks(text)])


def resolve(statements: list[Statement]) -> Program:
    prog = Program(statements=statements)
    defined_anywhere = {s.name for s in statements if isinstance(s, Def)}
    declared_at: dict[str, int] = {}
    defined_at: dict[str, int] = {}

    def expand(t: Term, line: int) -> Term:
        for name in sorted(free_vars(t) & defined_anywhere):
            if name not in prog.defs:
                raise TyperError(f"{name!r} is used before it is defined", line)
            t = subst(t, name, prog.defs[name])
        return t

    for s in statements:
        match s:
            case TypeDecl(var, ty, line):
                if var in declared_at:
                    raise TyperError(f"type of {var!r} already declared on line {declared_at[var]}", line)
                if var in defined_anywhere:
                    raise TyperError(f"{var!r} is a defined term, it cannot be given a type", line)
                declared_at[var] = line
                prog.env[var] = ty
            case Def(name, t, line):
                if name in defined_at:
                    raise TyperError(f"{name!r} already defined on line {defined_at[name]}", line)
                prog.defs[name] = expand(t, line)
                defined_at[name] = line
            case Canonical(t, source, line):
                prog.commands.append(Canonical(expand(t, line), source, line))
    return prog


def parse_file(path: str) -> Program:
    with open(path, encoding="utf-8") as f:
        return parse_program(f.read())
