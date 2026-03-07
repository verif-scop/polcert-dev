#!/usr/bin/env python3
from __future__ import annotations

import argparse
import dataclasses
import os
import re
from typing import Iterable, Iterator, Sequence


TOKEN_RE = re.compile(
    r"""
    (?P<SPACE>\s+)
  | (?P<LINECOMMENT>//[^\n]*)
  | (?P<BLOCKCOMMENT>/\*.*?\*/)
  | (?P<PLUSPLUS>\+\+)
  | (?P<PLUSEQ>\+=)
  | (?P<MINUSEQ>-=)
  | (?P<STAREQ>\*=)
  | (?P<SLASHEQ>/=)
  | (?P<LE><=)
  | (?P<GE>>=)
  | (?P<EQEQ>==)
  | (?P<NE>!=)
  | (?P<ANDAND>&&)
  | (?P<OROR>\|\|)
  | (?P<NUMBER>\d+\.\d+|\d+|\.\d+)
  | (?P<IDENT>[A-Za-z_][A-Za-z0-9_]*)
  | (?P<SYMBOL>[(){}\[\],;?:=+\-*/<>])
    """,
    re.S | re.X,
)


class ParseError(RuntimeError):
    pass


@dataclasses.dataclass(frozen=True)
class Token:
    kind: str
    text: str
    pos: int


def tokenize(text: str) -> list[Token]:
    out: list[Token] = []
    pos = 0
    while pos < len(text):
        m = TOKEN_RE.match(text, pos)
        if not m:
            raise ParseError(f"unexpected character at offset {pos}: {text[pos:pos+20]!r}")
        kind = m.lastgroup
        assert kind is not None
        if kind not in {"SPACE", "LINECOMMENT", "BLOCKCOMMENT"}:
            out.append(Token(kind, m.group(0), pos))
        pos = m.end()
    out.append(Token("EOF", "", len(text)))
    return out


@dataclasses.dataclass
class Number:
    text: str


@dataclasses.dataclass
class Name:
    name: str


@dataclasses.dataclass
class Access:
    base: str
    indices: list["Expr"]


@dataclasses.dataclass
class Unary:
    op: str
    expr: "Expr"


@dataclasses.dataclass
class Binary:
    op: str
    lhs: "Expr"
    rhs: "Expr"


@dataclasses.dataclass
class Call:
    name: str
    args: list["Expr"]


@dataclasses.dataclass
class Ternary:
    cond: "Cond"
    then_expr: "Expr"
    else_expr: "Expr"


@dataclasses.dataclass
class CondExpr:
    cond: "Cond"


Expr = Number | Name | Access | Unary | Binary | Call | Ternary | CondExpr


@dataclasses.dataclass
class Cmp:
    op: str
    lhs: Expr
    rhs: Expr


@dataclasses.dataclass
class Logic:
    op: str
    lhs: "Cond"
    rhs: "Cond"


Cond = Cmp | Logic


@dataclasses.dataclass
class AssignStmt:
    lhs: Access
    op: str
    rhs: Expr


@dataclasses.dataclass
class IfStmt:
    cond: Cond
    body: list["Stmt"]


@dataclasses.dataclass
class ForStmt:
    var: str
    lb: Expr
    ub: Expr
    body: list["Stmt"]


Stmt = AssignStmt | IfStmt | ForStmt


class Parser:
    def __init__(self, tokens: Sequence[Token]):
        self.tokens = list(tokens)
        self.i = 0

    def peek(self) -> Token:
        return self.tokens[self.i]

    def pop(self) -> Token:
        tok = self.peek()
        self.i += 1
        return tok

    def accept(self, kind: str, text: str | None = None) -> Token | None:
        tok = self.peek()
        if tok.kind != kind:
            return None
        if text is not None and tok.text != text:
            return None
        self.i += 1
        return tok

    def expect(self, kind: str, text: str | None = None) -> Token:
        tok = self.peek()
        if tok.kind != kind or (text is not None and tok.text != text):
            want = text if text is not None else kind
            raise ParseError(f"expected {want}, got {tok.text or tok.kind} at {tok.pos}")
        self.i += 1
        return tok

    def parse_program(self) -> list[Stmt]:
        out: list[Stmt] = []
        while self.peek().kind != "EOF":
            out.extend(self.parse_stmt_list_item())
        return out

    def parse_stmt_list_item(self) -> list[Stmt]:
        tok = self.peek()
        if tok.kind == "IDENT" and tok.text == "for":
            return [self.parse_for()]
        if tok.kind == "IDENT" and tok.text == "if":
            return [self.parse_if()]
        if tok.kind == "SYMBOL" and tok.text == "{":
            return self.parse_block()
        if tok.kind == "SYMBOL" and tok.text == ";":
            self.pop()
            return []
        return [self.parse_assign()]

    def parse_block(self) -> list[Stmt]:
        self.expect("SYMBOL", "{")
        out: list[Stmt] = []
        while not self.accept("SYMBOL", "}"):
            out.extend(self.parse_stmt_list_item())
        return out

    def parse_for(self) -> ForStmt:
        self.expect("IDENT", "for")
        self.expect("SYMBOL", "(")
        init_name, lb = self.parse_for_init()
        self.expect("SYMBOL", ";")
        cond_name, ub, inclusive = self.parse_for_cond()
        self.expect("SYMBOL", ";")
        step_name = self.parse_for_step()
        self.expect("SYMBOL", ")")
        if init_name != cond_name or init_name != step_name:
            raise ParseError(f"mismatched loop variable in for header: {init_name}, {cond_name}, {step_name}")
        if inclusive:
            ub = Binary("+", ub, Number("1"))
        body = self.parse_stmt_body()
        return ForStmt(init_name, lb, ub, body)

    def parse_for_init(self) -> tuple[str, Expr]:
        name = self.expect("IDENT").text
        self.expect("SYMBOL", "=")
        expr = self.parse_expr()
        return name, expr

    def parse_for_cond(self) -> tuple[str, Expr, bool]:
        lhs = self.parse_add()
        tok = self.pop()
        if tok.kind not in {"LE", "SYMBOL"} or tok.text not in {"<", "<="}:
            raise ParseError(f"unsupported loop comparison {tok.text} at {tok.pos}")
        rhs = self.parse_add()
        if not isinstance(lhs, Name):
            raise ParseError("loop condition lhs must be a variable")
        return lhs.name, rhs, tok.text == "<="

    def parse_for_step(self) -> str:
        if self.accept("PLUSPLUS"):
            return self.expect("IDENT").text
        name = self.expect("IDENT").text
        if self.accept("PLUSPLUS"):
            return name
        if self.accept("PLUSEQ"):
            one = self.parse_expr()
            if not is_one_expr(one):
                raise ParseError("only += 1 loop steps are supported")
            return name
        if self.accept("SYMBOL", "="):
            lhs = self.parse_expr()
            op = self.expect("SYMBOL").text
            rhs = self.parse_expr()
            if not (isinstance(lhs, Name) and lhs.name == name and op == "+" and is_one_expr(rhs)):
                raise ParseError("only i = i + 1 style loop steps are supported")
            return name
        raise ParseError(f"unsupported loop step after {name}")

    def parse_if(self) -> IfStmt:
        self.expect("IDENT", "if")
        self.expect("SYMBOL", "(")
        cond = self.parse_cond()
        self.expect("SYMBOL", ")")
        body = self.parse_stmt_body()
        return IfStmt(cond, body)

    def parse_stmt_body(self) -> list[Stmt]:
        if self.peek().kind == "SYMBOL" and self.peek().text == "{":
            return self.parse_block()
        return self.parse_stmt_list_item()

    def parse_assign(self) -> AssignStmt:
        lhs = self.parse_access()
        tok = self.pop()
        if tok.kind not in {"SYMBOL", "PLUSEQ", "MINUSEQ", "STAREQ", "SLASHEQ"}:
            raise ParseError(f"expected assignment operator at {tok.pos}, got {tok.text or tok.kind}")
        if tok.kind == "SYMBOL" and tok.text != "=":
            raise ParseError(f"expected assignment operator at {tok.pos}, got {tok.text}")
        op = tok.text
        rhs = self.parse_expr()
        self.expect("SYMBOL", ";")
        return AssignStmt(lhs, op, rhs)

    def parse_access(self) -> Access:
        base = self.expect("IDENT").text
        indices: list[Expr] = []
        while self.accept("SYMBOL", "["):
            idx = self.parse_expr()
            self.expect("SYMBOL", "]")
            indices.append(idx)
        return Access(base, indices)

    def parse_cond(self) -> Cond:
        lhs = self.parse_cmp()
        while self.accept("ANDAND"):
            lhs = Logic("&&", lhs, self.parse_cmp())
        return lhs

    def parse_cmp(self) -> Cond:
        lhs = self.parse_add()
        tok = self.pop()
        if tok.text not in {"<", "<=", "=="}:
            raise ParseError(f"unsupported condition operator {tok.text} at {tok.pos}")
        rhs = self.parse_add()
        op = tok.text
        if op == "<":
            rhs = Binary("-", rhs, Number("1"))
            op = "<="
        return Cmp(op, lhs, rhs)

    def parse_expr(self) -> Expr:
        return self.parse_ternary()

    def parse_ternary(self) -> Expr:
        lhs = self.parse_add()
        if isinstance(lhs, CondExpr):
            cond = lhs.cond
            if not (self.peek().kind == "SYMBOL" and self.peek().text == "?"):
                raise ParseError("comparisons are only supported in if-conditions or ternary conditions")
        else:
            cond = self.maybe_parse_expr_cond(lhs)
        if cond is not None:
            self.expect("SYMBOL", "?")
            then_expr = self.parse_expr()
            self.expect("SYMBOL", ":")
            else_expr = self.parse_expr()
            return Ternary(cond, then_expr, else_expr)
        return lhs

    def maybe_parse_expr_cond(self, lhs: Expr) -> Cond | None:
        tok = self.peek()
        if not (
            (tok.kind == "LE")
            or (tok.kind == "EQEQ")
            or (tok.kind == "SYMBOL" and tok.text in {"<", "==", "<="})
        ):
            return None
        tok = self.pop()
        op = tok.text
        rhs = self.parse_add()
        if op == "<":
            rhs = Binary("-", rhs, Number("1"))
            op = "<="
        cond: Cond = Cmp(op, lhs, rhs)
        while self.accept("ANDAND"):
            cond = Logic("&&", cond, self.parse_cmp())
        if not (self.peek().kind == "SYMBOL" and self.peek().text == "?"):
            raise ParseError("comparisons are only supported in if-conditions or ternary conditions")
        return cond

    def parse_add(self) -> Expr:
        lhs = self.parse_mul()
        while True:
            if self.accept("SYMBOL", "+"):
                lhs = Binary("+", lhs, self.parse_mul())
            elif self.accept("SYMBOL", "-"):
                lhs = Binary("-", lhs, self.parse_mul())
            else:
                return lhs

    def parse_mul(self) -> Expr:
        lhs = self.parse_unary()
        while True:
            if self.accept("SYMBOL", "*"):
                lhs = Binary("*", lhs, self.parse_unary())
            elif self.accept("SYMBOL", "/"):
                lhs = Binary("/", lhs, self.parse_unary())
            else:
                return lhs

    def parse_unary(self) -> Expr:
        if self.accept("SYMBOL", "-"):
            return Unary("-", self.parse_unary())
        return self.parse_primary()

    def parse_primary(self) -> Expr:
        tok = self.pop()
        if tok.kind == "NUMBER":
            return Number(tok.text)
        if tok.kind == "IDENT":
            name = tok.text
            if self.accept("SYMBOL", "("):
                args: list[Expr] = []
                if not self.accept("SYMBOL", ")"):
                    while True:
                        args.append(self.parse_expr())
                        if self.accept("SYMBOL", ","):
                            continue
                        self.expect("SYMBOL", ")")
                        break
                return Call(name, args)
            indices: list[Expr] = []
            while self.accept("SYMBOL", "["):
                idx = self.parse_expr()
                self.expect("SYMBOL", "]")
                indices.append(idx)
            if indices:
                return Access(name, indices)
            return Name(name)
        if tok.kind == "SYMBOL" and tok.text == "(":
            lhs = self.parse_add()
            tok2 = self.peek()
            if (tok2.kind == "LE") or (tok2.kind == "EQEQ") or (tok2.kind == "SYMBOL" and tok2.text in {"<", "==", "<="}):
                tok2 = self.pop()
                rhs = self.parse_add()
                op = tok2.text
                if op == "<":
                    rhs = Binary("-", rhs, Number("1"))
                    op = "<="
                cond: Cond = Cmp(op, lhs, rhs)
                while self.accept("ANDAND"):
                    cond = Logic("&&", cond, self.parse_cmp())
                self.expect("SYMBOL", ")")
                return CondExpr(cond)
            self.expect("SYMBOL", ")")
            return lhs
        raise ParseError(f"unexpected token in expression: {tok.text or tok.kind} at {tok.pos}")


def is_one_expr(expr: Expr) -> bool:
    return isinstance(expr, Number) and normalize_number(expr.text) == "1"


def normalize_number(text: str) -> str:
    if "." not in text:
        return str(int(text))
    value = float(text)
    if value == 0.0:
        return "0"
    if value > 0:
        return "1"
    return "-1"


def access_bases_expr(expr: Expr) -> list[str]:
    out: list[str] = []

    def go(e: Expr) -> None:
        if isinstance(e, Access):
            out.append(e.base)
            for idx in e.indices:
                go(idx)
            return
        if isinstance(e, Unary):
            go(e.expr)
            return
        if isinstance(e, Binary):
            go(e.lhs)
            go(e.rhs)
            return
        if isinstance(e, Call):
            for arg in e.args:
                go(arg)
            return
        if isinstance(e, CondExpr):
            go_cond(e.cond)
            return
        if isinstance(e, Ternary):
            go_cond(e.cond)
            go(e.then_expr)
            go(e.else_expr)

    def go_cond(c: Cond) -> None:
        if isinstance(c, Cmp):
            go(c.lhs)
            go(c.rhs)
        else:
            go_cond(c.lhs)
            go_cond(c.rhs)

    go(expr)
    return out


def free_names_expr(expr: Expr) -> list[str]:
    out: list[str] = []

    def go(e: Expr) -> None:
        if isinstance(e, Name):
            out.append(e.name)
            return
        if isinstance(e, Access):
            for idx in e.indices:
                go(idx)
            return
        if isinstance(e, Unary):
            go(e.expr)
            return
        if isinstance(e, Binary):
            go(e.lhs)
            go(e.rhs)
            return
        if isinstance(e, Call):
            for arg in e.args:
                go(arg)
            return
        if isinstance(e, CondExpr):
            go_cond(e.cond)
            return
        if isinstance(e, Ternary):
            go_cond(e.cond)
            go(e.then_expr)
            go(e.else_expr)

    def go_cond(c: Cond) -> None:
        if isinstance(c, Cmp):
            go(c.lhs)
            go(c.rhs)
        else:
            go_cond(c.lhs)
            go_cond(c.rhs)

    go(expr)
    return out


def expr_reads_as_expr(expr: Expr) -> Expr | None:
    terms: list[Expr] = []

    def add_term(e: Expr) -> None:
        terms.append(e)

    def go(e: Expr) -> None:
        if isinstance(e, (Number,)):
            return
        if isinstance(e, (Name, Access)):
            add_term(e)
            return
        if isinstance(e, Unary):
            go(e.expr)
            return
        if isinstance(e, Binary):
            go(e.lhs)
            go(e.rhs)
            return
        if isinstance(e, Call):
            for arg in e.args:
                go(arg)
            return
        if isinstance(e, CondExpr):
            go_cond(e.cond)
            return
        if isinstance(e, Ternary):
            go_cond(e.cond)
            go(e.then_expr)
            go(e.else_expr)

    def go_cond(c: Cond) -> None:
        if isinstance(c, Cmp):
            go(c.lhs)
            go(c.rhs)
        else:
            go_cond(c.lhs)
            go_cond(c.rhs)

    go(expr)
    if not terms:
        return None
    cur = terms[0]
    for term in terms[1:]:
        cur = Binary("+", cur, term)
    return cur


def to_affine(expr: Expr) -> str:
    if isinstance(expr, Number):
        return normalize_number(expr.text)
    if isinstance(expr, Name):
        return expr.name
    if isinstance(expr, Unary) and expr.op == "-":
        return f"(0 - {parenthesize_affine(expr.expr)})"
    if isinstance(expr, Binary) and expr.op in {"+", "-"}:
        return f"({to_affine(expr.lhs)} {expr.op} {to_affine(expr.rhs)})"
    if isinstance(expr, Binary) and expr.op == "*":
        if is_const_affine(expr.lhs):
            return f"({to_affine(expr.lhs)} * {parenthesize_affine(expr.rhs)})"
        if is_const_affine(expr.rhs):
            return f"({to_affine(expr.rhs)} * {parenthesize_affine(expr.lhs)})"
    raise ParseError(f"non-affine expression in affine position: {expr!r}")


def is_const_affine(expr: Expr) -> bool:
    if isinstance(expr, Number):
        return True
    if isinstance(expr, Unary) and expr.op == "-" and isinstance(expr.expr, Number):
        return True
    return False


def parenthesize_affine(expr: Expr) -> str:
    if isinstance(expr, (Number, Name)):
        return to_affine(expr)
    return to_affine(expr)


def to_expr(expr: Expr) -> str:
    if isinstance(expr, Number):
        return normalize_number(expr.text)
    if isinstance(expr, Name):
        return expr.name
    if isinstance(expr, Access):
        return expr.base + "".join(f"[{to_affine(idx)}]" for idx in expr.indices)
    if isinstance(expr, Unary) and expr.op == "-":
        return f"(0 - {parenthesize_expr(expr.expr)})"
    if isinstance(expr, Binary):
        if expr.op == "/":
            return f"({to_expr(expr.lhs)} * {to_expr(expr.rhs)})"
        return f"({to_expr(expr.lhs)} {expr.op} {to_expr(expr.rhs)})"
    if isinstance(expr, Call):
        collapsed = expr_reads_as_expr(expr)
        return "0" if collapsed is None else to_expr(collapsed)
    if isinstance(expr, CondExpr):
        collapsed = expr_reads_as_expr(expr)
        return "0" if collapsed is None else to_expr(collapsed)
    if isinstance(expr, Ternary):
        reads = expr_reads_as_expr(expr)
        return "0" if reads is None else to_expr(reads)
    raise ParseError(f"unsupported expression node: {expr!r}")


def parenthesize_expr(expr: Expr) -> str:
    if isinstance(expr, (Number, Name, Access)):
        return to_expr(expr)
    return to_expr(expr)


def to_cond(cond: Cond) -> str:
    if isinstance(cond, Logic):
        return f"({to_cond(cond.lhs)} && {to_cond(cond.rhs)})"
    assert isinstance(cond, Cmp)
    if cond.op == "==":
        return f"({to_affine(cond.lhs)} == {to_affine(cond.rhs)})"
    if cond.op == "<=":
        return f"({to_affine(cond.lhs)} <= {to_affine(cond.rhs)})"
    raise ParseError(f"unsupported condition operator: {cond.op}")


def assign_to_stmt(stmt: AssignStmt) -> str:
    lhs = stmt.lhs.base + "".join(f"[{to_affine(idx)}]" for idx in stmt.lhs.indices)
    lhs_expr: Expr = Access(stmt.lhs.base, stmt.lhs.indices)
    rhs = stmt.rhs
    if stmt.op == "+=":
        rhs = Binary("+", lhs_expr, rhs)
    elif stmt.op == "-=":
        rhs = Binary("-", lhs_expr, rhs)
    elif stmt.op == "*=":
        rhs = Binary("*", lhs_expr, rhs)
    elif stmt.op == "/=":
        rhs = Binary("*", lhs_expr, rhs)
    return f"{lhs} = {to_expr(rhs)};"


def stmt_to_loop(stmt: Stmt, indent: int = 0) -> list[str]:
    pad = "  " * indent
    if isinstance(stmt, AssignStmt):
        return [pad + assign_to_stmt(stmt)]
    if isinstance(stmt, IfStmt):
        out = [pad + f"if {to_cond(stmt.cond)} " + "{"]  # condition already parenthesized
        for inner in stmt.body:
            out.extend(stmt_to_loop(inner, indent + 1))
        out.append(pad + "}")
        return out
    assert isinstance(stmt, ForStmt)
    out = [pad + f"for {stmt.var} in range({to_affine(stmt.lb)}, {to_affine(stmt.ub)}) " + "{"] 
    for inner in stmt.body:
        out.extend(stmt_to_loop(inner, indent + 1))
    out.append(pad + "}")
    return out


def extract_scop_region(text: str) -> str:
    m = re.search(r"#pragma\s+scop(.*?)#pragma\s+endscop", text, re.S)
    if not m:
        raise ParseError("missing #pragma scop block")
    return m.group(1)


def ordered_unique(items: Iterable[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item not in seen:
            seen.add(item)
            out.append(item)
    return out


def collect_context(stmts: Sequence[Stmt]) -> list[str]:
    loop_vars: set[str] = set()
    names: list[str] = []

    def add_aff(e: Expr) -> None:
        for name in free_names_expr(e):
            if name not in loop_vars:
                names.append(name)

    def go_cond(c: Cond) -> None:
        if isinstance(c, Cmp):
            add_aff(c.lhs)
            add_aff(c.rhs)
        else:
            go_cond(c.lhs)
            go_cond(c.rhs)

    def go(st: Stmt) -> None:
        if isinstance(st, ForStmt):
            add_aff(st.lb)
            add_aff(st.ub)
            loop_vars.add(st.var)
            for inner in st.body:
                go(inner)
            loop_vars.remove(st.var)
            return
        if isinstance(st, IfStmt):
            go_cond(st.cond)
            for inner in st.body:
                go(inner)
            return
        assert isinstance(st, AssignStmt)
        for idx in st.lhs.indices:
            add_aff(idx)

    for stmt in stmts:
        go(stmt)
    return ordered_unique(names)


def convert_source(text: str) -> str:
    scop = extract_scop_region(text)
    parser = Parser(tokenize(scop))
    body = parser.parse_program()
    context = collect_context(body)
    lines: list[str] = []
    if context:
        lines.append("context(" + ", ".join(context) + ");")
        lines.append("")
    for stmt in body:
        lines.extend(stmt_to_loop(stmt, 0))
    lines.append("")
    return "\n".join(lines)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("src_root")
    ap.add_argument("dst_root")
    args = ap.parse_args()

    os.makedirs(args.dst_root, exist_ok=True)
    c_files = sorted(
        path
        for path in glob_c_files(args.src_root)
        if has_scop(path)
    )
    for path in c_files:
        name = os.path.basename(os.path.dirname(path))
        out_path = os.path.join(args.dst_root, f"{name}.loop")
        with open(path) as f:
            converted = convert_source(f.read())
        with open(out_path, "w") as f:
            f.write(converted)
    print(f"generated {len(c_files)} loop files into {args.dst_root}")
    return 0


def glob_c_files(root: str) -> Iterator[str]:
    for dirpath, _, filenames in os.walk(root):
        for name in sorted(filenames):
            if name.endswith(".c"):
                yield os.path.join(dirpath, name)


def has_scop(path: str) -> bool:
    with open(path) as f:
        return "#pragma scop" in f.read()


if __name__ == "__main__":
    raise SystemExit(main())
