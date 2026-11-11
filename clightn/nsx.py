# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Renders the neutral specification of N into Rocq and Lean, and checks what each prover
elaborated against it (clightn/README.md).

  uv run clightn/nsx.py render SPEC ROCQ_OUT LEAN_OUT
      writes the Rocq rendering (NSpec.v) and the Lean rendering (Spec.lean) of SPEC
  uv run clightn/nsx.py rocq-reader SPEC OUT [--no-proofs]
      writes the Rocq file (NRead.v) whose output the check reads
  uv run clightn/nsx.py check SPEC ROCQ_DIR LEAN_OUT [--no-proofs] [--expect KEY,...]
      compares the Rocq printouts in ROCQ_DIR and the Lean printout LEAN_OUT with SPEC
  uv run clightn/nsx.py mutate GROUP SRC OUT
      writes SRC with the planted errors of GROUP and prints the differences they must cause

The renderer is untrusted: the check reads back the terms that each prover elaborated, maps each
constant through the symbol table of SPEC, and compares the result with SPEC after the expansion
of macros, up to the names of bound variables.  A constant outside the table makes the comparison
fail.  With --expect, the check passes when the differences it finds are exactly the given ones.
"""
import os
import re
import sys

WIDTH = 100
ROCQ_SPEC, ROCQ_PROOF = "NSpec", "NProof"
LEAN_SPEC, LEAN_PROOF = "ClightN.Spec", "ClightN.Proof"
LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class SpecError(Exception):
    pass


# ---------------------------------------------------------------------------------------------
# S-expressions


def parse_all(text):
    toks = re.findall(r"\(|\)|[^\s()]+", re.sub(r";[^\n]*", "", text))
    pos = 0

    def one():
        nonlocal pos
        if pos >= len(toks):
            raise SpecError("unexpected end of input")
        t = toks[pos]
        pos += 1
        if t == ")":
            raise SpecError("unexpected )")
        if t != "(":
            return t
        out = []
        while pos < len(toks) and toks[pos] != ")":
            out.append(one())
        if pos >= len(toks):
            raise SpecError("missing )")
        pos += 1
        return out

    res = []
    while pos < len(toks):
        res.append(one())
    return res


def show(x):
    if isinstance(x, list):
        return "(" + " ".join(show(y) for y in x) + ")"
    return x


def is_num(t):
    return isinstance(t, str) and re.fullmatch(r"\d+", t) is not None


# ---------------------------------------------------------------------------------------------
# The specification

BINDERS = ("forall", "exists")
CONNECTIVES = {"->": 2, "and": 2, "or": 2, "iff": 2, "not": 1, "=": 2, "Some": 1}


class Spec:
    def __init__(self, path):
        self.sorts, self.symbols, self.macros = {}, {}, {}
        self.relations, self.statements = [], []
        for d in parse_all(open(path).read()):
            kind = d[0]
            if kind in ("sort", "data", "base", "interp"):
                names = {x[0]: x[1] for x in d[2:]}
                if set(names) != {"rocq", "lean"}:
                    raise SpecError(f"{d[1]}: needs a rocq and a lean name")
                if d[1] in self.sorts or d[1] in self.symbols:
                    raise SpecError(f"{d[1]}: declared twice")
                (self.sorts if kind == "sort" else self.symbols)[d[1]] = names
            elif kind == "macro":
                self.macros[d[1]] = (d[2], d[3])
            elif kind == "relation":
                self.relations.append(
                    (d[1], [(b[0], b[1]) for b in d[2]], d[3], [(c[1], c[2]) for c in d[4:]]))
            elif kind == "statement":
                self.statements.append((d[1], d[2]))
            else:
                raise SpecError(f"unknown declaration {kind}")
        for prover in ("rocq", "lean"):
            names = [show(n[prover]) for n in [*self.sorts.values(), *self.symbols.values()]]
            for n in names:
                if names.count(n) > 1:
                    raise SpecError(f"{n}: the {prover} name of two symbols")
        self.rel_names = {r[0] for r in self.relations}
        names = [c for r in self.relations for c, _ in r[3]] + [s for s, _ in self.statements]
        taken = set(self.sorts) | set(self.symbols) | self.rel_names
        for name in names:
            if name in taken or names.count(name) > 1:
                raise SpecError(f"{name}: declared twice")
        self.ctors, self.bodies = {}, {}
        for name, params, indices, ctors in self.relations:
            for s in [s for _, s in params] + indices:
                self.check_sort(s)
            for c, f in ctors:
                body = self.expand(f)
                self.validate(body, {p for p, _ in params})
                concl = body
                while isinstance(concl, list) and concl[0] in ("forall", "->"):
                    concl = concl[-1]
                if not (isinstance(concl, list) and concl[0] == name and
                        concl[1:1 + len(params)] == [p for p, _ in params] and
                        len(concl) == 1 + len(params) + len(indices)):
                    raise SpecError(f"{c}: the conclusion must apply {name} to its parameters "
                                    "and indices")
                self.ctors[c] = body
        for name, f in self.statements:
            self.bodies[name] = self.expand(f)
            self.validate(self.bodies[name], set())

    def expand(self, t, env=None):
        env = env or {}
        if isinstance(t, str):
            return env.get(t, t)
        if t and t[0] in BINDERS:
            return [t[0], [[b[0], self.expand(b[1], env)] for b in t[1]], self.expand(t[2], env)]
        if t and isinstance(t[0], str) and t[0] in self.macros:
            params, body = self.macros[t[0]]
            args = [self.expand(a, env) for a in t[1:]]
            if len(args) != len(params):
                raise SpecError(f"macro {t[0]} takes {len(params)} arguments")
            for a in args:
                clash = free_names(a) & bound_names(body)
                if clash:
                    raise SpecError(f"macro {t[0]} would capture {sorted(clash)}")
            return self.expand(body, dict(zip(params, args)))
        return [self.expand(a, env) for a in t]

    def check_sort(self, s):
        if isinstance(s, str):
            if s not in self.sorts:
                raise SpecError(f"unknown sort {s}")
        elif s[0] in ("option", "prod", "->") and len(s) == (2 if s[0] == "option" else 3):
            for x in s[1:]:
                self.check_sort(x)
        else:
            raise SpecError(f"bad sort {show(s)}")

    def validate(self, t, bound):
        """Every name of t is bound, a numeral, None, a symbol, or a relation in head position."""
        if isinstance(t, str):
            if t in bound or is_num(t) or t == "None" or t in self.symbols:
                return
            raise SpecError(f"unknown name {t}")
        if not t:
            raise SpecError("empty application")
        h = t[0]
        if h in BINDERS:
            inner = set(bound)
            for x, s in t[1]:
                self.check_sort(s)
                if x in self.symbols or x in self.sorts or x in self.rel_names or is_num(x) \
                        or x in CONNECTIVES or x in ("None", "_"):
                    raise SpecError(f"bound name {x} is a symbol")
                inner.add(x)
            return self.validate(t[2], inner)
        if h in CONNECTIVES and len(t) - 1 != CONNECTIVES[h]:
            raise SpecError(f"{h} takes {CONNECTIVES[h]} arguments")
        if not isinstance(h, str) or not (h in CONNECTIVES or h in self.symbols or
                                          h in self.rel_names or h in bound):
            raise SpecError(f"unknown head {show(h)}")
        for a in t[1:]:
            self.validate(a, bound)


def free_names(t):
    if isinstance(t, str):
        return {t}
    if t and t[0] in BINDERS:
        out = set()
        for _, s in t[1]:
            out |= free_names(s)
        return out | (free_names(t[2]) - {x for x, _ in t[1]})
    return set().union(*(free_names(a) for a in t)) if t else set()


def bound_names(t):
    if isinstance(t, str) or not t:
        return set()
    out = {x for x, _ in t[1]} if t[0] in BINDERS else set()
    return out.union(*(bound_names(a) for a in t))


# ---------------------------------------------------------------------------------------------
# Rendering, with lines of at most WIDTH characters.  A document is a string or a group
# (open, items, close), whose items go on one line when they fit and on separate lines otherwise.


def flat(d):
    if isinstance(d, str):
        return d
    return d[0] + " ".join(flat(x) for x in d[1]) + d[2]


def layout(d, col, indent, trail=0):
    """The text of d from column col, whose continuation lines start at indent + 2 or further,
    followed on its last line by trail characters."""
    f = flat(d)
    if isinstance(d, str) or col + len(f) + trail <= WIDTH:
        return f
    open_, items, close = d
    inner = indent + 2
    out = open_ + layout(items[0], col + len(open_), inner,
                         len(close) + trail if len(items) == 1 else 0)
    col = len(out.rsplit("\n", 1)[-1]) + (col if "\n" not in out else 0)
    for i, x in enumerate(items[1:], 1):
        after = len(close) + trail if i == len(items) - 1 else 0
        fx = flat(x)
        if col + 1 + len(fx) + after <= WIDTH:
            out += " " + fx
            col += 1 + len(fx)
        else:
            piece = layout(x, inner, inner, after)
            out += "\n" + " " * inner + piece
            last = piece.rsplit("\n", 1)[-1]
            col = len(last) + (inner if "\n" not in piece else 0)
    return out + close


class Renderer:
    def __init__(self, spec, prover):
        self.spec, self.p = spec, prover

    def name(self, sym, applied):
        """The name of sym, with every argument explicit when applied; a fixed application is
        parenthesized when it stands alone."""
        n = self.spec.symbols[sym][self.p]
        if isinstance(n, str):
            return "@" + n if applied else n
        return self.head(n) if applied else "(" + self.head(n) + ")"

    def head(self, h):
        if isinstance(h, str):
            return h
        return "@" + h[0] + " " + " ".join(self.head(x) if isinstance(x, str) else
                                           "(" + self.head(x) + ")" for x in h[1:])

    def sort(self, s):
        if isinstance(s, str):
            return self.spec.sorts[s][self.p]
        if s[0] == "option":
            return f"({'option' if self.p == 'rocq' else 'Option'} {self.sort(s[1])})"
        if s[0] == "prod":
            return f"({self.sort(s[1])} {'*' if self.p == 'rocq' else '×'} {self.sort(s[2])})"
        return f"({self.sort(s[1])} {'->' if self.p == 'rocq' else '→'} {self.sort(s[2])})"

    def term(self, t, bound):
        rocq = self.p == "rocq"
        if isinstance(t, str):
            if t in bound:
                return t
            if is_num(t):
                return f"({t})%Z" if rocq else f"({t} : Int)"
            if t == "None":
                return "(@None _)" if rocq else "(@Option.none _)"
            return self.name(t, False)
        h = t[0]
        if h in BINDERS:
            inner = bound | {x for x, _ in t[1]}
            q = {"forall": ("forall", "∀"), "exists": ("exists", "∃")}[h][0 if rocq else 1]
            bs = [f"({x} : {self.sort(s)})" for x, s in t[1]]
            return ("(", [(q + " ", bs, ","), self.term(t[2], inner)], ")")
        args = [self.term(a, bound) for a in t[1:]]
        if h in ("->", "and", "or", "iff"):
            op = {"->": ("->", "→"), "and": ("/\\", "∧"), "or": ("\\/", "∨"),
                  "iff": ("<->", "↔")}[h][0 if rocq else 1]
            return ("(", [args[0], (op + " ", [args[1]], "")], ")")
        if h == "not":
            return ("(", [("~ " if rocq else "¬ ", [args[0]], "")], ")")
        if h == "=":
            return ("(", ["@eq _" if rocq else "@Eq _"] + args, ")")
        if h == "Some":
            return ("(", ["@Some _" if rocq else "@Option.some _"] + args, ")")
        if h in self.spec.rel_names or h in bound:
            return ("(", [h] + args, ")")
        return ("(", [self.name(h, True)] + args, ")")


def render(spec, rocq_path, lean_path):
    out = {"rocq": ["(* Rendered by clightn/nsx.py from clightn/N.nsx.  Do not edit. *)",
                    "From Coq Require Import ZArith.",
                    "Require Coqlib Integers Values AST Memory Ctypes Cop Clight.",
                    "Require NBase.", ""],
           "lean": ["-- Rendered by clightn/nsx.py from clightn/N.nsx.  Do not edit.",
                    "import LeanExe.Native.ClightN.Base", "", "set_option autoImplicit false", "",
                    f"namespace {LEAN_SPEC}", ""]}
    for p, lines in out.items():
        r = Renderer(spec, p)
        rocq = p == "rocq"
        arrow = " ->" if rocq else " →"
        for name, params, indices, ctors in spec.relations:
            ps = "".join(f" ({x} : {r.sort(s)})" for x, s in params)
            items = [r.sort(s) + arrow for s in indices] + ["Prop :=" if rocq else "Prop where"]
            head = f"{'Inductive' if rocq else 'inductive'} {name}{ps} :"
            lines.append(layout(("", [head] + items, ""), 0, 2))
            for i, (c, _) in enumerate(ctors):
                pre = f"  | {c} : "
                end = "." if rocq and i == len(ctors) - 1 else ""
                lines.append(pre + layout(r.term(spec.ctors[c], {x for x, _ in params}),
                                          len(pre), 2, len(end)) + end)
            lines.append("")
        for name, _ in spec.statements:
            end = "." if rocq else ""
            body = layout(r.term(spec.bodies[name], set()), 2, 2, len(end))
            lines.append(f"Definition stmt_{name} : Prop :=" if rocq else f"def stmt_{name} : Prop :=")
            lines.append("  " + body + end)
            lines.append("")
    out["lean"].append(f"end {LEAN_SPEC}")
    open(rocq_path, "w").write("\n".join(out["rocq"]).rstrip() + "\n")
    open(lean_path, "w").write("\n".join(out["lean"]).rstrip() + "\n")


def rocq_reader(spec, path, proofs=True):
    lines = ["(* Generated by clightn/nsx.py: prints, for the check, the terms that Rocq",
             "   elaborated, with every argument explicit, one file for each. *)",
             "Require NBase NSpec." + (" Require NProof." if proofs else ""),
             "Require Compiler.", "Set Printing All.", "Set Printing Width 1000000.",
             "Set Printing Depth 1000000."]
    for name, _, _, ctors in spec.relations:
        lines.append(f'Redirect "rocq.relation.{name}" Print {ROCQ_SPEC}.{name}.')
        lines.append(f'Redirect "rocq.arity.{name}" Check @{ROCQ_SPEC}.{name}.')
        for c, _ in ctors:
            lines.append(f'Redirect "rocq.ctor.{c}" Check @{ROCQ_SPEC}.{c}.')
    for name, _ in spec.statements:
        lines.append(f'Redirect "rocq.statement.{name}" Print {ROCQ_SPEC}.stmt_{name}.')
        if proofs:
            lines.append(f'Redirect "rocq.proof.{name}" Check {ROCQ_PROOF}.{name}.')
            lines.append(f'Redirect "rocq.assumptions.{name}" Print Assumptions {ROCQ_PROOF}.{name}.')
    lines.append('Redirect "rocq.reference" Print Assumptions Compiler.transf_c_program_correct.')
    open(path, "w").write("\n".join(lines) + "\n")


# ---------------------------------------------------------------------------------------------
# Canonical forms: binders one at a time, bound variables as their de Bruijn levels #k, a product
# whose variable is unused as an implication, and every constant as its neutral symbol.


def uses(t, x):
    """Whether the raw term t mentions the name x free, with binders (kind, [(name, sort)], body)."""
    if isinstance(t, str):
        return t.lstrip("@") == x
    if t and t[0] in ("forall", "exists", "fun"):
        for y, s in t[1]:
            if uses(s, x):
                return True
            if y == x:
                return False
        return uses(t[2], x)
    return any(uses(a, x) for a in t)


def binder(kind, binders, body, scope, sort_fn, term_fn):
    """The canonical form of a binder list over body, by the functions for sorts and terms."""
    if not binders:
        return term_fn(body, scope)
    (x, s), rest = binders[0], binders[1:]
    inner = [kind, rest, body] if rest else body
    if kind == "forall" and (x == "_" or not uses(inner, x)):
        return ["->", sort_fn(s, scope), binder(kind, rest, body, scope, sort_fn, term_fn)]
    level = f"#{len(scope)}"
    return [kind, sort_fn(s, scope), binder(kind, rest, body, scope + [(x, level)], sort_fn, term_fn)]


def lookup(scope, x):
    for name, level in reversed(scope):
        if name == x:
            return level
    return None


def spec_sort(s, scope=None):
    if isinstance(s, str):
        return s
    return [s[0]] + [spec_sort(x) for x in s[1:]]


def spec_canon(t, scope):
    if isinstance(t, str):
        return lookup(scope, t) or t
    if t[0] in BINDERS:
        return binder(t[0], t[1], t[2], scope, spec_sort, spec_canon)
    return [spec_canon(a, scope) for a in t]


def spec_forms(spec):
    """The canonical form of every declaration, keyed by kind and name."""
    forms = {}
    for name, params, indices, ctors in spec.relations:
        arity = "Prop"
        for s in reversed(indices):
            arity = ["->", s, arity]
        forms[("relation", name)] = (spec_canon(["forall", params, arity], []) if params else
                                     spec_canon(arity, []))
        for c, _ in ctors:
            body = spec.ctors[c]
            forms[("ctor", c)] = spec_canon(["forall", params, body] if params else body, [])
    for name, _ in spec.statements:
        forms[("statement", name)] = spec_canon(spec.bodies[name], [])
    return forms


# Rocq: terms printed under Set Printing All.

def rocq_tokens(s):
    return re.findall(r"\(|\)|=>|->|,|:|@?[A-Za-z_][A-Za-z0-9_'.]*|\d+", s)


class RocqParser:
    def __init__(self, text):
        self.t, self.i = rocq_tokens(text), 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        if self.i >= len(self.t):
            raise SpecError("Rocq term ends early")
        tok = self.t[self.i]
        if x is not None and tok != x:
            raise SpecError(f"Rocq term: expected {x}, found {tok}")
        self.i += 1
        return tok

    def binders(self, stop):
        bs = []
        if self.peek() == "(":
            while self.peek() == "(":
                self.eat("(")
                names = []
                while self.peek() != ":":
                    names.append(self.eat())
                self.eat(":")
                s = self.term()
                self.eat(")")
                bs += [(n, s) for n in names]
        else:
            names = []
            while self.peek() != ":":
                names.append(self.eat())
            self.eat(":")
            s = self.term(stop=(stop,))
            bs = [(n, s) for n in names]
        return bs

    def term(self, stop=()):
        tok = self.peek()
        if tok in ("forall", "fun"):
            self.eat()
            sep = "," if tok == "forall" else "=>"
            bs = self.binders(sep)
            self.eat(sep)
            return [tok, bs, self.term(stop)]
        left = self.app(stop)
        if self.peek() == "->":
            self.eat()
            return ["->", left, self.term(stop)]
        return left

    def app(self, stop):
        items = []
        while self.peek() not in (None, ")", ",", "=>", "->", ":") and self.peek() not in stop:
            tok = self.eat()
            if tok == "(":
                items.append(self.term())
                self.eat(")")
            else:
                items.append(tok)
        if not items:
            raise SpecError("Rocq term: empty application")
        return items[0] if len(items) == 1 else items

    def whole(self):
        t = self.term()
        if self.peek() is not None:
            raise SpecError(f"Rocq term: trailing {self.peek()}")
        return t


def positive(t):
    if t == "BinNums.xH":
        return 1
    if isinstance(t, list) and len(t) == 2 and t[0] in ("BinNums.xO", "BinNums.xI"):
        return 2 * positive(t[1]) + (t[0] == "BinNums.xI")
    raise SpecError(f"not a positive literal: {show(t)}")


class RocqNorm:
    def __init__(self, spec):
        self.table = {}
        for name, names in list(spec.sorts.items()) + list(spec.symbols.items()):
            self.table[names["rocq"]] = name
        for name in spec.rel_names:
            self.table[f"{ROCQ_SPEC}.{name}"] = name
        for name, _ in spec.statements:
            self.table[f"{ROCQ_SPEC}.stmt_{name}"] = "stmt_" + name
        self.table["Prop"] = "Prop"

    def sort(self, s, scope):
        return self.term(s, scope)

    def term(self, t, scope):
        if isinstance(t, str):
            name = t.lstrip("@")
            level = lookup(scope, name)
            if level:
                return level
            if name == "BinNums.Z0":
                return "0"
            return self.table.get(name, "?" + name)
        h = t[0]
        if h in ("forall", "fun"):
            if h == "fun":
                raise SpecError("Rocq term: a function outside an existential")
            return binder("forall", t[1], t[2], scope, self.sort, self.term)
        if h == "->":
            return ["->", self.term(t[1], scope), self.term(t[2], scope)]
        name = h.lstrip("@") if isinstance(h, str) else None
        if name == "BinNums.Zpos" and len(t) == 2:
            return str(positive(t[1]))
        if name == "eq" and len(t) == 4:
            return ["=", self.term(t[2], scope), self.term(t[3], scope)]
        if name == "Some" and len(t) == 3:
            return ["Some", self.term(t[2], scope)]
        if name == "None" and len(t) == 2:
            return "None"
        if name == "ex" and len(t) == 3 and isinstance(t[2], list) and t[2][0] == "fun" \
                and len(t[2][1]) == 1:
            return binder("exists", t[2][1], t[2][2], scope, self.sort, self.term)
        if name in ("and", "or", "iff", "not"):
            return [name] + [self.term(a, scope) for a in t[1:]]
        if name in ("option", "prod"):
            return [name] + [self.term(a, scope) for a in t[1:]]
        return [self.term(a, scope) for a in t]


def rocq_file(d, name):
    path = os.path.join(d, name + ".out")
    if not os.path.exists(path):
        return None
    return open(path).read()


def rocq_check_output(text):
    """NAME and TYPE of the output 'NAME\\n : TYPE' of Check."""
    m = re.fullmatch(r"(\S+)\s*\n\s+: (.*?)\s*", text, re.S)
    if not m:
        raise SpecError(f"unexpected Check output: {text[:200]}")
    return m.group(1), m.group(2)


def rocq_forms(spec, d, proofs):
    norm = RocqNorm(spec)
    got, notes = {}, {}

    def term(text):
        return norm.term(RocqParser(text).whole(), [])

    for name, _, _, ctors in spec.relations:
        text = rocq_file(d, f"rocq.relation.{name}")
        if text is None:
            notes[("relation", name)] = "printed nothing"
            continue
        m = re.match(r"(\w+) (\S+)[^\n]*?:=(.*?)\.\s*(\n\n|$)", text, re.S)
        if not m or m.group(2) != name:
            notes[("relation", name)] = f"unexpected Print output: {text[:200]}"
            continue
        if m.group(1) not in ("Inductive", "Variant"):
            notes[("relation", name)] = f"is a {m.group(1)}, not an inductive relation"
        names = [re.match(r"\s*(\S+) :", piece).group(1) for piece in m.group(3).split(" | ")]
        if names != [c for c, _ in ctors]:
            notes[("constructors", name)] = f"has the constructors {' '.join(names)}"
        text = rocq_file(d, f"rocq.arity.{name}")
        if text is not None:
            n, ty = rocq_check_output(text)
            got[("relation", name)] = term(ty) if n == f"{ROCQ_SPEC}.{name}" else "?" + n
        for c in names:
            text = rocq_file(d, f"rocq.ctor.{c}")
            if text is not None:
                n, ty = rocq_check_output(text)
                got[("ctor", c)] = term(ty) if n == f"{ROCQ_SPEC}.{c}" else "?" + n
    for name, _ in spec.statements:
        text = rocq_file(d, f"rocq.statement.{name}")
        if text is not None:
            m = re.fullmatch(r"(\S+) = (.*)\n\s+: (\S+)\s*", text, re.S)
            if not m or m.group(1) != f"{ROCQ_SPEC}.stmt_{name}" or m.group(3) != "Prop":
                notes[("statement", name)] = f"unexpected Print output: {text[:200]}"
            else:
                got[("statement", name)] = term(m.group(2))
        if proofs:
            text = rocq_file(d, f"rocq.proof.{name}")
            if text is not None:
                n, ty = rocq_check_output(text)
                got[("proof", name)] = term(ty) if n == f"{ROCQ_PROOF}.{name}" else "?" + n
            text = rocq_file(d, f"rocq.assumptions.{name}")
            if text is not None:
                got[("assumptions", name)] = assumption_names(text)
    if proofs:
        ref = rocq_file(d, "rocq.reference")
        got["reference"] = assumption_names(ref) if ref is not None else None
    return got, notes


def assumption_names(text):
    return {m.group(1) for m in re.finditer(r"^([A-Za-z][A-Za-z0-9_.']*)( :|$)", text, re.M)}


# Lean: the S-expressions that ClightN.Read.dump writes, with every argument explicit.

class LeanNorm:
    def __init__(self, spec):
        self.table, self.heads = {}, []
        for name, names in list(spec.sorts.items()) + list(spec.symbols.items()):
            n = names["lean"]
            if isinstance(n, str):
                self.table[n] = name
            else:
                self.heads.append((n, name))
        for name in spec.rel_names:
            self.table[f"{LEAN_SPEC}.{name}"] = name
        for name, _ in spec.statements:
            self.table[f"{LEAN_SPEC}.stmt_{name}"] = "stmt_" + name
        self.table["Prop"] = "Prop"

    def sort(self, s, scope):
        return self.term(s, scope)

    def term(self, t, scope):
        if isinstance(t, str):
            level = lookup(scope, t)
            if level:
                return level
            return self.table.get(t, "?" + t)
        h = t[0]
        if h in ("forall", "fun"):
            if h == "fun":
                raise SpecError("Lean term: a function outside an existential")
            return binder("forall", [tuple(b) for b in t[1]], t[2], scope, self.sort, self.term)
        if h == "->":
            return ["->", self.term(t[1], scope), self.term(t[2], scope)]
        if h == "OfNat.ofNat" and len(t) == 4 and t[1] == "Int" and t[2][0] == "lit" \
                and t[3] == ["instOfNat", t[2]]:
            return t[2][1]
        if h == "Eq" and len(t) == 4:
            return ["=", self.term(t[2], scope), self.term(t[3], scope)]
        if h == "Option.some" and len(t) == 3:
            return ["Some", self.term(t[2], scope)]
        if h == "Option.none" and len(t) == 2:
            return "None"
        if h == "Exists" and len(t) == 3 and isinstance(t[2], list) and t[2][0] == "fun" \
                and len(t[2][1]) == 1:
            return binder("exists", [tuple(b) for b in t[2][1]], t[2][2], scope, self.sort,
                          self.term)
        conn = {"And": "and", "Or": "or", "Iff": "iff", "Not": "not", "Option": "option",
                "Prod": "prod"}
        if h in conn:
            return [conn[h]] + [self.term(a, scope) for a in t[1:]]
        for head, name in self.heads:
            if t[:len(head)] == head:
                return [name] + [self.term(a, scope) for a in t[len(head):]]
        return [self.term(a, scope) for a in t]


def lean_forms(spec, path, proofs):
    norm = LeanNorm(spec)
    got, notes = {}, {}
    for line in open(path):
        if not line.strip():
            continue
        d = parse_all(line)[0]
        kind, full = d[0], d[1]
        if kind == "relation":
            name = full.removeprefix(LEAN_SPEC + ".")
            got[("relation", name)] = norm.term(d[2], [])
            ctors = [c.removeprefix(f"{full}.") for c in d[3][1:]]
            rel = next((r for r in spec.relations if r[0] == name), None)
            if rel is None:
                notes[("relation", name)] = "is not in the specification"
            elif ctors != [c for c, _ in rel[3]]:
                notes[("constructors", name)] = f"has the constructors {' '.join(ctors)}"
            if d[4] != "safe":
                notes[("relation", name)] = "is unsafe"
        elif kind == "ctor":
            got[("ctor", full.rsplit(".", 1)[1])] = norm.term(d[2], [])
        elif kind == "statement":
            name = full.removeprefix(f"{LEAN_SPEC}.stmt_")
            got[("statement", name)] = norm.term(d[2], [])
            if d[3] != "Prop":
                notes[("statement", name)] = f"has the type {show(d[3])}"
            if not any(n == name for n, _ in spec.statements):
                notes[("statement", name)] = "is not in the specification"
        elif kind == "proof" and proofs:
            name = full.removeprefix(LEAN_PROOF + ".")
            got[("proof", name)] = norm.term(d[2], [])
            got[("assumptions", name)] = set(d[3][1:])
        elif kind in ("no-proof", "not-theorem") and proofs:
            notes[("proof", full.removeprefix(LEAN_PROOF + "."))] = \
                "is missing" if kind == "no-proof" else "is not a theorem"
        elif kind == "other":
            notes[("declaration", full)] = "is not a relation or statement of the specification"
    return got, notes


# ---------------------------------------------------------------------------------------------
# The check


def check(spec, rocq_dir, lean_out, proofs=True, expect=None):
    want = spec_forms(spec)
    found = set()
    reports = []

    def differ(prover, kind, name, message):
        found.add(f"{prover}:{kind}:{name}")
        reports.append(f"clightn: {prover}'s {kind} {name} {message}")

    for prover, (got, notes) in (("Rocq", rocq_forms(spec, rocq_dir, proofs)),
                                 ("Lean", lean_forms(spec, lean_out, proofs))):
        for (kind, name), message in notes.items():
            differ(prover, kind, name, message)
        for key, form in want.items():
            if key not in got:
                if key not in notes:
                    differ(prover, key[0], key[1], "was not printed")
            elif got[key] != form:
                differ(prover, key[0], key[1], "differs from the specification\n"
                       f"  spec: {show(form)}\n  {prover}: {show(got[key])}")
        if not proofs:
            continue
        allowed = LEAN_AXIOMS if prover == "Lean" else got.get("reference")
        if allowed is None:
            differ(prover, "reference", "transf_c_program_correct", "was not printed")
            allowed = set()
        for name, _ in spec.statements:
            if ("proof", name) in notes:
                continue
            if ("proof", name) not in got:
                differ(prover, "proof", name, "is missing")
            elif got[("proof", name)] != "stmt_" + name:
                differ(prover, "proof", name, f"proves {show(got[('proof', name)])}, "
                       f"not stmt_{name}")
            extra = got.get(("assumptions", name), set()) - allowed
            if extra:
                differ(prover, "proof", name, f"assumes {' '.join(sorted(extra))}")
    for r in reports:
        print(r)
    nctors = sum(len(r[3]) for r in spec.relations)
    counts = (f"{len(spec.relations)} relations with {nctors} constructors and "
              f"{len(spec.statements)} statements")
    if expect is not None:
        if found == expect:
            print(f"clightn: the check found exactly the {len(expect)} planted differences")
            return 0
        print(f"clightn: planted but not found: {' '.join(sorted(expect - found)) or 'none'}")
        print(f"clightn: found but not planted: {' '.join(sorted(found - expect)) or 'none'}")
        return 1
    if found:
        print(f"clightn: {counts}; {len(found)} differences")
        return 1
    if proofs:
        print(f"clightn: {counts} agree in Rocq and Lean; each statement is proved in both, with "
              "the permitted assumptions")
    else:
        print(f"clightn: {counts} agree in Rocq and Lean")
    return 0


# ---------------------------------------------------------------------------------------------
# Planted errors.  A group edits one file: each edit replaces OLD by NEW inside the declaration
# DECL, where OLD must occur exactly once, and names the difference that the check must report.

MUTATIONS = {
    "lean-spec": [
        ("bo_add_ul", "(@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd)",
         "(@HSub.hSub Int Int Int (@instHSub Int Int.instSub)", "Lean:ctor:bo_add_ul"),
        ("bo_shl_ul", "(64 : Int)", "(63 : Int)", "Lean:ctor:bo_shl_ul"),
        ("co_ul_uc", "(256 : Int)", "((256 : Nat) : Int)", "Lean:ctor:co_ul_uc"),
        ("bo_sub_ui", "(@ClightN.Base.u32 x)\n            (@ClightN.Base.u32 y)",
         "(@ClightN.Base.u32 y)\n            (@ClightN.Base.u32 x)", "Lean:ctor:bo_sub_ui"),
        ("bo_sub_ul",
         "(@HSub.hSub Int Int Int (@instHSub Int Int.instSub) (@ClightN.Base.u64 x)\n"
         "            (@ClightN.Base.u64 y))",
         "(((@ClightN.Base.u64 x).toNat - (@ClightN.Base.u64 y).toNat : Nat) : Int)",
         "Lean:ctor:bo_sub_ul"),
        ("co_ui_vui", "Bool.true", "Bool.false", "Lean:ctor:co_ui_vui"),
    ],
    "rocq-spec": [
        ("bo_mul_ul", "BinInt.Z.mul", "BinInt.Z.add", "Rocq:ctor:bo_mul_ul"),
        ("bool_ok", "Inductive bool_ok", "CoInductive bool_ok", "Rocq:relation:bool_ok"),
        ("bv_ui_false", "  | bv_ui_false :",
         "  | bv_extra : (forall (x : Integers.Int.int), (bool_ok\n"
         "      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))\n"
         "      (@Values.Vint x) true))\n  | bv_ui_false :", "Rocq:constructors:bool_ok"),
    ],
    "lean-proof": [
        ("lt_ul_ul", "theorem lt_ul_ul : stmt_lt_ul_ul := by",
         "theorem lt_ul_ul : ∀ (ce : Unit) (v1 v2 v : val) (m : mem),\n"
         "    binop_ok .Olt tul tul v1 v2 v → binop_ok .Olt tul tul v1 v2 v := by\n"
         "  intro _ _ _ _ _ h\n  exact h\n\ntheorem lt_ul_ul_unused : stmt_lt_ul_ul := by",
         "Lean:proof:lt_ul_ul"),
        ("mul_ul_ul", "theorem mul_ul_ul : stmt_mul_ul_ul := by",
         "theorem mul_ul_ul : stmt_mul_ul_ul := by\n  sorry\n\n"
         "theorem mul_ul_ul_unused : stmt_mul_ul_ul := by", "Lean:proof:mul_ul_ul"),
    ],
    "rocq-proof": [
        ("div_ul_ul", "Theorem div_ul_ul : stmt_div_ul_ul.",
         "Theorem div_ul_ul : forall v1 v2 v,\n"
         "  binop_ok Odiv tulong tulong v1 v2 v -> binop_ok Odiv tulong tulong v1 v2 v.\n"
         "Proof. auto. Qed.\n\nTheorem div_ul_ul_unused : stmt_div_ul_ul.",
         "Rocq:proof:div_ul_ul"),
        ("cast_ul_ui", "Theorem cast_ul_ui : stmt_cast_ul_ui.\nProof.",
         "Theorem cast_ul_ui : stmt_cast_ul_ui.\nProof.\nAdmitted.\n\n"
         "Theorem cast_ul_ui_unused : stmt_cast_ul_ui.\nProof.", "Rocq:proof:cast_ul_ui"),
    ],
}

DECL_START = r"^(\s*\| {name} :|(def|theorem|inductive|Definition|Theorem|Inductive) {name}\b)"
DECL_NEXT = r"^(\s*\| \S+ :|(def|theorem|inductive|Definition|Theorem|Lemma|Inductive|end) |$)"


def mutate(group, src, out):
    """Writes SRC with the planted errors of GROUP to OUT, and prints the differences that the
    check must report.  A Lean file also imports the reader and calls it."""
    text = open(src).read()
    keys = []
    for decl, old, new, key in MUTATIONS[group]:
        m = re.search(DECL_START.format(name=re.escape(decl)), text, re.M)
        if not m:
            raise SpecError(f"{group}: no declaration {decl}")
        rest = text[m.end():]
        n = re.search(DECL_NEXT, rest, re.M)
        end = m.end() + (n.start() if n else len(rest))
        block = text[m.start():end]
        if block.count(old) != 1:
            raise SpecError(f"{group}: {decl} holds the text to replace {block.count(old)} times")
        text = text[:m.start()] + block.replace(old, new) + text[end:]
        keys.append(key)
    if group.startswith("lean"):
        lines = text.split("\n")
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines.insert(last + 1, "import LeanExe.Native.ClightN.Read")
        text = "\n".join(lines) + "\nrun_cmd ClightN.Read.dump\n"
    open(out, "w").write(text)
    print(",".join(keys))


def main(argv):
    try:
        cmd, args = argv[1], argv[2:]
        flags = {a for a in args if a == "--no-proofs"}
        expect = None
        if "--expect" in args:
            i = args.index("--expect")
            expect = set(args[i + 1].split(","))
            args = args[:i] + args[i + 2:]
        args = [a for a in args if a not in flags]
        if cmd == "render" and len(args) == 3:
            render(Spec(args[0]), args[1], args[2])
        elif cmd == "rocq-reader" and len(args) == 2:
            rocq_reader(Spec(args[0]), args[1], "--no-proofs" not in flags)
        elif cmd == "check" and len(args) == 3:
            return check(Spec(args[0]), args[1], args[2], "--no-proofs" not in flags, expect)
        elif cmd == "mutate" and len(args) == 3:
            mutate(*args)
        else:
            print(__doc__, file=sys.stderr)
            return 2
    except SpecError as e:
        print(f"clightn: {e}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
