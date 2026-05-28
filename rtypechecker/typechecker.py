"""
Parser for Simply-Typed Lambda Calculus expressions.

Grammar:
    Type     ::= BaseType | IType '->' Type | '(' Type ')'
    IType    ::= { Type,..., Type }
    TType    ::= [Type,..., Type]
    BaseType::= [A-Z][a-zA-Z0-9]*

    Term    ::= Atom | Term Atom          (application, left-associative)
    Atom    ::= Var
              | 'fun ' Var ':' Type '.' Term
              | '(' Term ')'
    Var     ::= [a-z][a-zA-Z0-9]*

Examples:
    fun x:A. x
    fun f:A->B. fun x:A. f x
    (fun x:A. x) y
"""

from __future__ import annotations

from builtins import frozenset
from dataclasses import dataclass
from typing import Optional
import re


# ---------------------------------------------------------------------------
# AST nodes
# ---------------------------------------------------------------------------

@dataclass(frozen=True)
class TyBase:
    """A base type, e.g. A, Bool, Nat."""
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass(frozen=True)
class TyArrow:
    """A function type sigma1 -> T2."""
    domain: "IType"
    codomain: "Type"

    def __str__(self) -> str:
        dom = f"({self.domain})" if isinstance(self.domain, IType) else str(self.domain)
        return f"{dom} -> {self.codomain}"

@dataclass(frozen=True)
class IType:
    """A intersection type { T1,..., Tn }."""
    els: list["Type"] # "Elements of Type"

    def __str__(self) -> str:
        res= "{"
        for el in self.els:
            res+=f"({el})" if isinstance(el, Type) else str(self.el)
        return res + "}"

@dataclass
class TType:
    """A tuple type [ T1,..., Tn ]."""
    eltyp = "Type"
    els: list[eltyp] #"Elements of a tuple type"

    def __str__(self) -> str:
        res= "["
        for el in self.els[0:-1]:
            res+=f"{el}, " if isinstance(el, eltyp) else str(el)
        return res + f"{self.els[-1]}]"
    
    def get_domain(self) -> eltyp:
        tpl = []
        for el in self.els:
            if isinstance(el, TyArrow):
                tpl.append(el.domain)
            else:
                raise TypeError(f"Expected a function type in tuple, got {el}")
        return TIType(tpl)
    
    def dimension(self) -> int:
        return len(self.els)

    

@dataclass
class TIType(TType):
    """A tuple intersection type [ {T1},..., {Tn} ]."""
    eltyp = "IType"
    
    def get_domain(self) -> list[list[Type]]:
        tpl = []
        for el in self.els:
            inintr = []
            for el_el in el.els:
                if isinstance(el_el, TyArrow):
                    inintr.append(el_el.domain)
            tpl.append(inintr)
        return tpl
    
    def tolist(self) -> list[TType]:
        ll = [[x] for x in self.els[0].els]   
        for i in range(1,len(self.els)):
            if not isinstance(self.els[i], IType):
                raise TypeError(f"Expected an intersection type in tuple, got {self.els[i]}")
            nl = ll.copy()
            for j in range(len(self.els[i].els)):
                el_el = self.els[i].els[j]
                if not isinstance(el_el, Type):
                    raise TypeError(f"Expected a type in intersection, got {el_el}")
                strat = [lelem + [el_el] for lelem in nl]
                ll.extend(strat)
        res = []
        for i in ll:
            res.append(TType(i))
        return res

Type = TyBase | TyArrow


@dataclass
class Var:
    """A variable."""
    name: str

    def __str__(self) -> str:
        return self.name


@dataclass
class Lam:
    """A lambda abstraction fun x:T. body."""
    var: str
    ty: Type
    body: "Term"

    def __str__(self) -> str:
        return f"(fun {self.var}:{self.ty}. {self.body})"


@dataclass
class App:
    """An application (fun arg)."""
    fun: "Term"
    arg: "Term"

    def __str__(self) -> str:
        return f"({self.fun} {self.arg})"


@dataclass
class Let:
    var: str
    value: "Term"
    body: "Term"

    def __str__(self) -> str:
        return f"(let {self.var} = {self.value} in {self.body})"

Term = Var | Lam | App | Let


# ---------------------------------------------------------------------------
# Tokeniser
# ---------------------------------------------------------------------------

_TOKEN_PATTERNS = [
    ("LAMBDA",   r"fun |\\"),
    ("ARROW",    r"->|→"),
    ("LBRACE",   r"\{"),
    ("RBRACE",   r"\}"),
    ("LBRACKET",  r"\["),
    ("RBRACKET",  r"\]"),
    ("COMMA",     r","),
    ("DOT",       r"\."),
    ("COLON",     r":"),
    ("LPAREN",    r"\("),
    ("RPAREN",    r"\)"),
    ("UPPER",     r"[A-Z][a-zA-Z0-9_]*"),   # base types
    ("LOWER",     r"[a-z][a-zA-Z0-9_]*"),   # variables
    ("SKIP",      r"\s+"),
    ("LET",      r"let"),
    ("IN",       r"in"),
    ("EQ",       r"="),
]

_TOKEN_RE = re.compile(
    "|".join(f"(?P<{name}>{pat})" for name, pat in _TOKEN_PATTERNS)
)


class Token:
    __slots__ = ("kind", "value", "pos")

    def __init__(self, kind: str, value: str, pos: int) -> None:
        self.kind = kind
        self.value = value
        self.pos = pos

    def __repr__(self) -> str:
        return f"Token({self.kind!r}, {self.value!r})"


def tokenise(src: str) -> list[Token]:
    tokens: list[Token] = []
    for m in _TOKEN_RE.finditer(src):
        kind = m.lastgroup
        if kind == "SKIP":
            continue
        tokens.append(Token(kind, m.group(), m.start()))
    return tokens


# ---------------------------------------------------------------------------
# Parser
# ---------------------------------------------------------------------------

class ParseError(Exception):
    pass


class Parser:
    """
    Recursive-descent parser for simply-typed lambda calculus.

    Type grammar (right-associative ->):
        type  ::= itype '->' type | tatom
        tatom ::= LOWER | '(' type ')'
        itype ::= '{' itypet
        itypet ::= '}' | type "," itypet
        ttype ::= '[' ttypet
        ttypet ::= ']' | type "," ttypet
        titype ::= '[' titypet
        titypet ::= ']' | itype "," titypet

    Term grammar (left-associative application):
        term  ::= atom+
        atom  ::= LOWER
                | 'fun ' LOWER ':' type '.' term
                | '(' term ')'
    """

    def __init__(self, src: str) -> None:
        self._tokens = tokenise(src)
        self._pos = 0

    # --- helpers ---

    def _peek(self) -> Optional[Token]:
        if self._pos < len(self._tokens):
            return self._tokens[self._pos]
        return None

    def _consume(self, *kinds: str) -> Token:
        tok = self._peek()
        if tok is None:
            raise ParseError(
                f"Unexpected end of input; expected one of {kinds}"
            )
        if tok.kind not in kinds:
            raise ParseError(
                f"Expected {kinds} at position {tok.pos}, got {tok.kind!r} ({tok.value!r})"
            )
        self._pos += 1
        return tok

    def _at(self, *kinds: str) -> bool:
        tok = self._peek()
        return tok is not None and tok.kind in kinds

    # --- type parser ---

    def parse_type(self) -> Type:
        """type  ::= itype '->' type | tatom"""
        if self._at("LOWER") or self._at("LPAREN"):
            target = self.parse_tatom()
            return target
        else:
            left = self.parse_itype()
        if self._at("ARROW"):
            self._consume("ARROW")
            right = self.parse_type()          # right-associative
            return TyArrow(left, right)
        tok = self._peek()
        pos = tok.pos if tok else "EOF"
        raise ParseError(f"Expected an arrow at position {pos}")

    def parse_type(self) -> Type:
        """type  ::= itype '->' type | tatom"""
        if self._at("LOWER") or self._at("LPAREN"):
            target = self.parse_tatom()
            return target
        else:
            left = self.parse_itype()
        if self._at("ARROW"):
            self._consume("ARROW")
            right = self.parse_type()          # right-associative
            return TyArrow(left, right)
        tok = self._peek()
        pos = tok.pos if tok else "EOF"
        raise ParseError(f"Expected an arrow at position {pos}")

    def parse_tatom(self) -> Type:
        """atype ::= LOWER | '(' type ')'"""
        if self._at("LOWER"):
            tok = self._consume("LOWER")
            return TyBase(tok.value)
        if self._at("LPAREN"):
            self._consume("LPAREN")
            ty = self.parse_type()
            self._consume("RPAREN")
            return ty
        tok = self._peek()
        pos = tok.pos if tok else "EOF"
        raise ParseError(f"Expected a type at position {pos}")

    def parse_ttype(self) -> Type:
        """ttype ::= '[' tttype
           tttype ::= ']' | type "," tttype"""
        if self._at("LBRACKET"):
            self._consume("LBRACKET")
            ty = self._parse_ttypet()
            return TType(ty)
        tok = self._peek()
        pos = tok.pos if tok else "EOF"
        raise ParseError("Expected [ at position " + str(pos))

    def _parse_ttypet(self) -> Type:
        """ttypet ::= ']' | type "," ttypet"""
        tps = []
        while not self._at("RBRACKET"):
            tp = self.parse_type()
            tps.append(tp)
            if self._at("COMMA"):
                self._consume("COMMA")
                continue
            if not self._at("RBRACKET"):
                tok = self._peek()
                pos = tok.pos if tok else "EOF"
                raise ParseError("Expected comma or ] at position" + f"{pos}")
        self._consume("RBRACKET")
        return tps
    
    def parse_titype(self) -> Type:
        """titype ::= '[' titypet
           titypet ::= ']' | itype ']' | itype "," titypet"""
        if self._at("LBRACKET"):
            self._consume("LBRACKET")
            ty = self._parse_titypet()
            return TIType(ty)
        tok = self._peek()
        pos = tok.pos if tok else "EOF"
        raise ParseError("Expected [ at position " + str(pos))

    def _parse_titypet(self) -> Type:
        """titypet ::= ']' | itype "," titypet"""
        tps = []
        while not self._at("RBRACKET"):
            tp = self.parse_itype()
            tps.append(tp)
            if self._at("COMMA"):
                self._consume("COMMA")
                continue
            if not self._at("RBRACKET"):
                tok = self._peek()
                pos = tok.pos if tok else "EOF"
                raise ParseError("Expected comma or ] at position" + f"{pos}")
        self._consume("RBRACKET")
        return tps

    def parse_itype(self) -> Type:
        """itype ::= '{' itypet
           itypet ::= '}' | itype '}' | itype "," itypet"""
        if self._at("LBRACE"):
            self._consume("LBRACE")
            ty = self._parse_itypet()
            return IType(ty)
        tok = self._peek()
        pos = tok.pos if tok else "EOF"
        raise ParseError("Expected { at position " + str(pos))

    def _parse_itypet(self) -> Type:
        """itypet ::= '}' | type '}' | type "," itypet"""
        tps = []
        while not self._at("RBRACE"):
            tp: TyBase | TyArrow = self.parse_type()
            tps.append(tp)
            if self._at("COMMA"):
                self._consume("COMMA")
                continue
            if not self._at("RBRACE"):
                tok = self._peek()
                pos = tok.pos if tok else "EOF"
                raise ParseError("Expected comma or } at position" + f"{pos}")
        self._consume("RBRACE")
        return tps

    # --- term parser ---

    def parse_term(self) -> Term:
        """term ::= atom+   (left-associative application)"""
        atoms: list[Term] = []
        while self._peek() is not None and not self._at("RPAREN"):
            atoms.append(self._parse_atom())
            if not atoms:
                break
        if not atoms:
            tok = self._peek()
            pos = tok.pos if tok else "EOF"
            raise ParseError(f"Expected a term at position {pos}")
        result = atoms[0]
        for a in atoms[1:]:
            result = App(result, a)
        return result

    def _parse_atom(self) -> Term:
        """atom ::= LOWER | 'fun ' LOWER ':' abstype '.' term | '(' term ')'"""
        tok = self._peek()
        if tok is None:
            raise ParseError("Unexpected end of input while parsing atom")

        if tok.kind == "LOWER":
            self._consume("LOWER")
            return Var(tok.value)

        if tok.kind == "LAMBDA":
            self._consume("LAMBDA")
            var_tok = self._consume("LOWER")
            self._consume("COLON")
            ty = self.parse_titype()
            self._consume("DOT")
            body = self.parse_term()
            return Lam(var_tok.value, ty, body)

        if tok.kind == "LPAREN":
            self._consume("LPAREN")
            term = self.parse_term()
            self._consume("RPAREN")
            return term
        
        if tok.kind == "LET":
            self._consume("LET")
            var_tok = self._consume("LOWER")
            self._consume("EQ")
            value = self.parse_term()
            self._consume("IN")
            body = self.parse_term()
            return Let(var_tok.value, value, body)

        raise ParseError(
            f"Unexpected token {tok.kind!r} ({tok.value!r}) at position {tok.pos}"
        )

    def parse(self) -> Term:
        """Parse the entire input as a term."""
        term = self.parse_term()
        if self._peek() is not None:
            tok = self._peek()
            raise ParseError(
                f"Unexpected trailing token {tok.kind!r} ({tok.value!r}) at position {tok.pos}"
            )
        return term


# ---------------------------------------------------------------------------
# Convenience functions
# ---------------------------------------------------------------------------

def parse(src: str) -> Term:
    """Parse a typed lambda calculus expression from a string."""
    return Parser(src).parse()


def parse_type(src: str) -> Type:
    """Parse a type expression from a string."""
    p = Parser(src)
    ty = p.parse_type()
    if p._peek() is not None:
        tok = p._peek()
        raise ParseError(f"Trailing token {tok.kind!r} at position {tok.pos}")
    return ty


# ---------------------------------------------------------------------------
# Type-checker
# ---------------------------------------------------------------------------

def desugar(term: Term) -> Term:
    if isinstance(term, Let):
        # let x = t1 in t2  ≡  (fun x:T. t2) t1
        # UWAGA: T nieznany → użyjemy typu inferowanego później
        return App(
            Lam(term.var, TyBase("_"), desugar(term.body)),
            desugar(term.value),
        )
    if isinstance(term, Lam):
        return Lam(term.var, term.ty, desugar(term.body))
    if isinstance(term, App):
        return App(desugar(term.fun), desugar(term.arg))
    return term

Ctx = dict[str, Type]

def functionlike(fun_ty : TType) -> bool:
    """Check if fun_ty is a function-like type, i.e. 
       a TType whose elements are TyArrow."""
    if not isinstance(fun_ty, TType):
        return False
    for el in fun_ty.els:
        if not isinstance(el, TyArrow):
            return False
    return True

def types_match(fntp : TType, argtypes : list[TType]) -> TType | None:
    """Check if function of fntp can be applied to at least one of argtypes, 
       i.e. if the domain of each arrow in the vector fntp matches some type in one of argtypes."""
    for argtype in argtypes:
        res = []
        for i1 in range(len(fntp.els)):
            domain = fntp.els[i1].domain
            for el1_el in domain.els:
                if not isinstance(el1_el, Type):
                    return False
                if any(_types_equal(el1_el, eil2) for eil2 in argtype.els):
                    continue
                else:
                    domain = None
                    break
            if domain is None:
                res = None
                break
            else:
                res.append(fntp.els[i1].codomain)
        if res is not None:
            return TType(res)
    return None

def vector_arrow(argtype : TIType, bodytypes : list[TType]) -> list[TType]:
    res = []
    for bodytype in bodytypes:
        nels = []
        for el1,el2 in zip(argtype.els,bodytype.els):
            nels.append(TyArrow(el1,el2))
        res.append(TType(nels))
    return res
    
def dimension(ty: list[TType]) -> int:
    if not ty:
        return 0
    dim = ty[0].dimension()
    for el in ty:
        if dim != el.dimension():
            raise TypeError(f"Dimension mismatch: expected {dim} but got {el.dimension()}")
    return dim

def type_check(term: Term, ctx: Ctx | None = None) -> list[TType]:
    """Type-check a term in the given context, returning list of potential vector types."""

    if ctx is None:
        ctx = {}

    if isinstance(term, Var):
        if term.name not in ctx:
            raise TypeError(f"Unbound variable: {term.name!r}")
        return ctx[term.name].tolist()

    if isinstance(term, Lam):
        new_ctx = {**ctx, term.var: term.ty}
        body_ty = type_check(term.body, new_ctx)
        if dimension(body_ty) != term.ty.dimension():
            raise TypeError(
                f"Dimension mismatch: lambda body has type dimension {dimension(body_ty)} but expected {term.ty.dimension()}"
            )
        return vector_arrow(term.ty, body_ty)

    if isinstance(term, App):
        fun_ty : list[TType] = type_check(term.fun, ctx)
        arg_ty : list[TType] = type_check(term.arg, ctx)
        res = []
        for ty in fun_ty:
            if not functionlike(ty):
                continue
            match = types_match(ty, arg_ty)
            if match is not None:
                res.append(match)
        return res

    #if isinstance(term, Let):
    #    val_ty = type_check(term.value, ctx)
    #    new_ctx = {**ctx, term.var: val_ty}
    #    return type_check(term.body, new_ctx)

    raise TypeError(f"Unknown term type: {type(term)}")


def _types_equal(t1: Type, t2: Type) -> bool:
    if type(t1) != type(t2):
        return False
    if isinstance(t1, TyBase) and isinstance(t2, TyBase):
        return t1.name == t2.name
    if isinstance(t1, TyArrow) and isinstance(t2, TyArrow):
        return _types_equal(t1.domain, t2.domain) and _types_equal(t1.codomain, t2.codomain)
    if isinstance(t1, IType) and isinstance(t2, IType):
        return t1.els == t2.els
    return False

def presentation(ty: list[TType]) -> str:
    if not ty:
        return "No types"
    return "\n * " + " \n * ".join(str(t) for t in ty)

# ---------------------------------------------------------------------------
# Demo
# ---------------------------------------------------------------------------

if __name__ == "__main__":
    examples = [
        # (expression, free-variable context for type-checking)
        (r"fun x:[{a}]. x",                  {}),
        (r"fun f:[{{a}->b}]. fun x:[{a}]. f x",       {}),
        (r"fun x:[{a}]. fun y:[{b}]. x",            {}),
        (r"(fun x:[{a}]. x) y",              {"y": TIType([IType({TyBase("a")})])}),
        (r"fun f:[{{a}->b}]. fun g:[{{b}->c}]. fun x:[{a}]. g (f x)", {}),
        (r"fun p:[{{({a}->b)}->a}]. fun q:[{{a}->b}]. q (p q)",  {}),
    ]

    print(f"{'Expression':<60}  {'AST (str)':<60}  Type")
    print("-" * 100)
    for src, ctx in examples:
        try:
            term = parse(src)
            term = desugar(term)
            ty = type_check(term, ctx)
            print(f"{src:<40}  {str(term):<40}  {presentation(ty)}")
        except (ParseError, TypeError) as e:
            print(f"{src:<40}  ERROR: {e}")

