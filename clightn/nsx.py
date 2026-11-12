# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Renders the neutral specification of N into Rocq and Lean, and checks what each prover
elaborated against it (clightn/README.md).

  uv run clightn/nsx.py render SPECS ROCQ_OUTS LEAN_OUTS
      writes the Rocq rendering and the Lean rendering of each file of SPECS
  uv run clightn/nsx.py rocq-reader SPECS OUT [--no-proofs]
      writes the Rocq file (NRead.v) whose output the check reads
  uv run clightn/nsx.py check SPECS ROCQ_DIR LEAN_OUT [--no-proofs] [--expect KEY,...]
      compares the Rocq printouts in ROCQ_DIR and the Lean printout LEAN_OUT with SPECS
  uv run clightn/nsx.py mutate GROUP SRC OUT [FORM]
      writes SRC with the planted errors of GROUP and prints the differences they must cause;
      FORM, the form of an instance's statement, selects the planted errors of an instance's group
  uv run clightn/nsx.py equations SPEC
      prints the floating-point equations of SPEC, which the proofs assume

SPECS, ROCQ_OUTS, and LEAN_OUTS are lists separated by commas: the specification of N, then the
files that extend it, such as a program and its statement, each with its two renderings.

The renderer is untrusted: the check reads back the terms that each prover elaborated, maps each
constant through the symbol table of SPEC, and compares the result with SPEC after the expansion
of macros, up to the names of bound variables.  A constant outside the table makes the comparison
fail.  With --expect, the check passes when the differences it finds are exactly the given ones.

An equation (equation NAME SORT (rocq R) (lean L)) is a symbol whose two meanings, R in Rocq and L
in Lean, the specification assumes to agree on every argument.  Each rendering defines eqn_NAME of
the sort SORT as the symbol, the check confirms both definitions, and it names the equations as
the assumptions of the proofs.
"""
import os
import re
import sys
import threading

WIDTH = 100
ROCQ_SPEC, ROCQ_PROOF = "NSpec", "NProof"
LEAN_SPEC, LEAN_PROOF = "ClightN.Spec", "ClightN.Proof"
LEAN_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


class SpecError(Exception):
    pass


# ---------------------------------------------------------------------------------------------
# S-expressions


def parse_all(text):
    toks = re.findall(r'\(|\)|"[A-Za-z0-9_]*"|[^\s()"]+', re.sub(r";[^\n]*", "", text))
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


def is_str(t):
    return isinstance(t, str) and re.fullmatch(r'"[A-Za-z0-9_]*"', t) is not None


# ---------------------------------------------------------------------------------------------
# The specification

BINDERS = ("forall", "exists")
CONNECTIVES = {"->": 2, "and": 2, "or": 2, "iff": 2, "not": 1, "=": 2, "Some": 1, "cons": 2,
               "pair": 2}
ATOMS = ("None", "nil")


class Spec:
    """The declarations of one or more files.  The first file renders to NSpec.v and Spec.lean;
    each further file declares (part (rocq MODULE)) and renders to the Rocq module MODULE and a
    Lean module of the namespace ClightN.Spec that imports Spec.lean."""

    def __init__(self, paths):
        self.sorts, self.symbols, self.macros = {}, {}, {}
        self.relations, self.statements, self.constants, self.equations = [], [], [], []
        self.modules = [ROCQ_SPEC]
        for part, path in enumerate(paths):
            for d in parse_all(open(path).read()):
                kind = d[0]
                if kind == "part":
                    if part == 0 or len(self.modules) != part:
                        raise SpecError("part: only the first declaration of a further file")
                    self.modules.append(dict(x for x in d[1:])["rocq"])
                    continue
                if part > 0 and len(self.modules) != part + 1:
                    raise SpecError(f"{path}: a further file starts with (part (rocq MODULE))")
                if kind in ("sort", "data", "base", "interp", "equation"):
                    if kind == "equation":
                        if part > 0:
                            raise SpecError(f"{d[1]}: equations belong in the first file")
                        self.equations.append((d[1], d[2]))
                        d = [d[0], d[1]] + d[3:]
                    names = {x[0]: x[1] for x in d[2:]}
                    if set(names) != {"rocq", "lean"}:
                        raise SpecError(f"{d[1]}: needs a rocq and a lean name")
                    if d[1] in self.sorts or d[1] in self.symbols:
                        raise SpecError(f"{d[1]}: declared twice")
                    (self.sorts if kind == "sort" else self.symbols)[d[1]] = names
                elif kind == "macro":
                    self.macros[d[1]] = (d[2], d[3])
                elif kind == "relation":
                    if part > 0:
                        raise SpecError(f"{d[1]}: relations belong in the first file")
                    self.relations.append(
                        (d[1], [(b[0], b[1]) for b in d[2]], d[3], [(c[1], c[2]) for c in d[4:]]))
                elif kind == "statement":
                    self.statements.append((d[1], d[2], part, None))
                elif kind == "carried":
                    self.statements.append((d[1], d[3], part, dict([d[2]])["rocq"]))
                elif kind == "constant":
                    if d[1] in self.symbols:
                        raise SpecError(f"{d[1]}: declared twice")
                    self.constants.append((d[1], d[2], d[3], part))
                    self.symbols[d[1]] = {"rocq": f"{self.modules[part]}.cst_{d[1]}",
                                          "lean": f"{LEAN_SPEC}.cst_{d[1]}", "constant": True}
                else:
                    raise SpecError(f"unknown declaration {kind}")
        for prover in ("rocq", "lean"):
            names = [show(n[prover]) for n in [*self.sorts.values(), *self.symbols.values()]]
            for n in names:
                if names.count(n) > 1:
                    raise SpecError(f"{n}: the {prover} name of two symbols")
        self.rel_names = {r[0] for r in self.relations}
        names = [c for r in self.relations for c, _ in r[3]] + [s[0] for s in self.statements]
        taken = set(self.sorts) | set(self.symbols) | self.rel_names
        for name in names:
            if name in taken or names.count(name) > 1:
                raise SpecError(f"{name}: declared twice")
        self.relations = [(name, [(x, self.expand(s)) for x, s in params],
                           [self.expand(s) for s in indices], ctors)
                          for name, params, indices, ctors in self.relations]
        self.ctors, self.bodies, self.values = {}, {}, {}
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
        self.eqsorts = {}
        for name, sort in self.equations:
            self.eqsorts[name] = self.expand(sort)
            self.check_sort(self.eqsorts[name])
        for name, sort, value, _ in self.constants:
            sort = self.expand(sort)
            self.check_sort(sort)
            self.values[name] = (sort, self.expand(value))
            self.validate(self.values[name][1], set())
        for name, f, _, _ in self.statements:
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
        elif s[0] in ("option", "list", "prod", "->") and \
                len(s) == (2 if s[0] in ("option", "list") else 3):
            for x in s[1:]:
                self.check_sort(x)
        else:
            raise SpecError(f"bad sort {show(s)}")

    def validate(self, t, bound):
        """Every name of t is bound, a numeral, a string, None, nil, a symbol, or a relation in
        head position, and (lit ident N) is a numeral of identifiers."""
        if isinstance(t, str):
            if t in bound or is_num(t) or is_str(t) or t in ATOMS or t in self.symbols:
                return
            raise SpecError(f"unknown name {t}")
        if not t:
            raise SpecError("empty application")
        h = t[0]
        if h == "lit":
            if len(t) != 3 or t[1] != "ident" or not is_num(t[2]) or t[2] == "0":
                raise SpecError(f"bad numeral {show(t)}")
            return
        if h in BINDERS:
            inner = set(bound)
            for x, s in t[1]:
                self.check_sort(s)
                if x in self.symbols or x in self.sorts or x in self.rel_names or is_num(x) \
                        or x in CONNECTIVES or x in ATOMS or x in ("_", "lit"):
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
# Continuation lines are indented by the depth of their group, up to MAX_INDENT columns, so that
# deep program literals keep their lines within WIDTH.  The length of a group on one line is
# kept for each group, and its text is formed only when it fits, since the texts of all the
# nested groups of a deep literal together take memory in proportion to its size times its depth.

MAX_INDENT = 40
_FLAT_LEN = {}


def flat(d):
    if isinstance(d, str):
        return d
    return d[0] + " ".join(flat(x) for x in d[1]) + d[2]


def flat_len(d):
    if isinstance(d, str):
        return len(d)
    k = id(d)
    if k not in _FLAT_LEN:
        _FLAT_LEN[k] = (d, len(d[0]) + sum(flat_len(x) for x in d[1]) +
                        max(len(d[1]) - 1, 0) + len(d[2]))
    return _FLAT_LEN[k][1]


def layout(d, col, indent, trail=0):
    """The text of d from column col, whose continuation lines start at indent + 2 or further,
    followed on its last line by trail characters."""
    if isinstance(d, str):
        return d
    if col + flat_len(d) + trail <= WIDTH:
        return flat(d)
    open_, items, close = d
    inner = min(indent + 2, MAX_INDENT)
    out = open_ + layout(items[0], col + len(open_), inner,
                         len(close) + trail if len(items) == 1 else 0)
    col = len(out.rsplit("\n", 1)[-1]) + (col if "\n" not in out else 0)
    for i, x in enumerate(items[1:], 1):
        after = len(close) + trail if i == len(items) - 1 else 0
        nx = flat_len(x)
        if col + 1 + nx + after <= WIDTH:
            out += " " + flat(x)
            col += 1 + nx
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
        """The document of the sort s."""
        rocq = self.p == "rocq"
        if isinstance(s, str):
            n = self.spec.sorts[s][self.p]
            return n if isinstance(n, str) else ("(", self.head(n).split(" "), ")")
        if s[0] in ("option", "list"):
            return ("(", [s[0] if rocq else s[0].capitalize(), self.sort(s[1])], ")")
        op = {"prod": ("*", "×"), "->": ("->", "→")}[s[0]][0 if rocq else 1]
        return ("(", [self.sort(s[1]), (op + " ", [self.sort(s[2])], "")], ")")

    def binding(self, x, s):
        return ("(", [f"{x} :", self.sort(s)], ")")

    def term(self, t, bound):
        rocq = self.p == "rocq"
        if isinstance(t, str):
            if t in bound:
                return t
            if is_num(t):
                return f"({t})%Z" if rocq else f"({t} : Int)"
            if is_str(t):
                return f"({t}%string)" if rocq else t
            if t == "None":
                return "(@None _)" if rocq else "(@Option.none _)"
            if t == "nil":
                return "(@nil _)" if rocq else "(@List.nil _)"
            return self.name(t, False)
        h = t[0]
        if h == "lit":
            return f"({t[2]})%positive" if rocq else f"({t[2]} : LClight.ident)"
        if h in BINDERS:
            inner = bound | {x for x, _ in t[1]}
            q = {"forall": ("forall", "∀"), "exists": ("exists", "∃")}[h][0 if rocq else 1]
            bs = [self.binding(x, s) for x, s in t[1]]
            return ("(", [(q + " ", bs, ","), self.term(t[2], inner)], ")")
        args = [self.term(a, bound) for a in t[1:]]
        if h in ("->", "and", "or", "iff"):
            op = {"->": ("->", "→"), "and": ("/\\", "∧"), "or": ("\\/", "∨"),
                  "iff": ("<->", "↔")}[h][0 if rocq else 1]
            return ("(", [args[0], (op + " ", [args[1]], "")], ")")
        if h == "not":
            return ("(", [("~ " if rocq else "¬ ", [args[0]], "")], ")")
        fixed = {"=": ("@eq _", "@Eq _"), "Some": ("@Some _", "@Option.some _"),
                 "cons": ("@cons _", "@List.cons _"), "pair": ("@pair _ _", "@Prod.mk _ _")}
        if h in fixed:
            return ("(", [fixed[h][0 if rocq else 1]] + args, ")")
        if h in self.spec.rel_names or h in bound:
            return ("(", [h] + args, ")")
        return ("(", [self.name(h, True)] + args, ")")


def render(spec, rocq_paths, lean_paths):
    """Writes the rendering of each file of spec: the first to NSpec.v and Spec.lean, each
    further one to its Rocq module and to a Lean module that imports Spec.lean."""
    sys.setrecursionlimit(1000000)
    for part, (rocq_path, lean_path) in enumerate(zip(rocq_paths, lean_paths)):
        requires = "Require NBase." if part == 0 else "Require NBase NSpec.\nImport NSpec."
        imports = "import LeanExe.Native.ClightN." + ("Base" if part == 0 else "Spec")
        out = {"rocq": ["(* Rendered by clightn/nsx.py from the specification of N.  Do not "
                        "edit. *)",
                        "From Coq Require Import ZArith String.",
                        "Require Coqlib Integers Floats Values AST Memory Events Ctypes Cop "
                        "Clight ClightBigstep.", requires, ""],
               "lean": ["-- Rendered by clightn/nsx.py from the specification of N.  Do not edit.",
                        imports, "", "set_option autoImplicit false",
                        "set_option maxRecDepth 100000"] +
                       (["set_option maxHeartbeats 0"] if part > 0 else []) +
                       ["", f"namespace {LEAN_SPEC}", ""]}
        for p, lines in out.items():
            r = Renderer(spec, p)
            rocq = p == "rocq"
            arrow = " ->" if rocq else " →"
            for name, _ in (spec.equations if part == 0 else []):
                lines.append(layout(("", [f"{'Definition' if rocq else 'def'} eqn_{name} :",
                                          r.sort(spec.eqsorts[name]), ":="], ""), 0, 2))
                lines.append("  " + r.name(name, False) + ("." if rocq else ""))
                lines.append("")
            for name, params, indices, ctors in (spec.relations if part == 0 else []):
                ps = [r.binding(x, s) for x, s in params]
                items = [("", [r.sort(s)], arrow) for s in indices] + \
                    ["Prop :=" if rocq else "Prop where"]
                head = [f"{'Inductive' if rocq else 'inductive'} {name}"] + ps + [":"]
                lines.append(layout(("", head + items, ""), 0, 2))
                for i, (c, _) in enumerate(ctors):
                    pre = f"  | {c} : "
                    end = "." if rocq and i == len(ctors) - 1 else ""
                    lines.append(pre + layout(r.term(spec.ctors[c], {x for x, _ in params}),
                                              len(pre), 2, len(end)) + end)
                lines.append("")
            end = "." if rocq else ""
            for name, _, _, cpart in spec.constants:
                if cpart != part:
                    continue
                sort, value = spec.values[name]
                lines.append(layout(("", [f"{'Definition' if rocq else 'def'} cst_{name} :",
                                          r.sort(sort), ":="], ""), 0, 2))
                lines.append("  " + layout(r.term(value, set()), 2, 2, len(end)) + end)
                lines.append("")
            for name, _, spart, _ in spec.statements:
                if spart != part:
                    continue
                body = layout(r.term(spec.bodies[name], set()), 2, 2, len(end))
                lines.append(f"Definition stmt_{name} : Prop :=" if rocq else
                             f"def stmt_{name} : Prop :=")
                lines.append("  " + body + end)
                lines.append("")
        out["lean"].append(f"end {LEAN_SPEC}")
        open(rocq_path, "w").write("\n".join(out["rocq"]).rstrip() + "\n")
        open(lean_path, "w").write("\n".join(out["lean"]).rstrip() + "\n")


def rocq_reader(spec, path, proofs=True):
    carried = sorted({c.rsplit(".", 1)[0] for _, _, _, c in spec.statements if c})
    requires = " ".join(["NBase"] + spec.modules +
                        (["NProof"] + carried + ["Compiler"] if proofs else []))
    lines = ["(* Generated by clightn/nsx.py: prints, for the check, the terms that Rocq",
             "   elaborated, with every argument explicit, one file for each. *)",
             f"Require {requires}.", "Set Printing All.", "Set Printing Width 1000000.",
             "Set Printing Depth 1000000."]
    for name, _, _, ctors in spec.relations:
        lines.append(f'Redirect "rocq.relation.{name}" Print {ROCQ_SPEC}.{name}.')
        lines.append(f'Redirect "rocq.arity.{name}" Check @{ROCQ_SPEC}.{name}.')
        for c, _ in ctors:
            lines.append(f'Redirect "rocq.ctor.{c}" Check @{ROCQ_SPEC}.{c}.')
    for name, _ in spec.equations:
        lines.append(f'Redirect "rocq.equation.{name}" Print {ROCQ_SPEC}.eqn_{name}.')
    for name, _, _, part in spec.constants:
        lines.append(f'Redirect "rocq.constant.{name}" Print {spec.modules[part]}.cst_{name}.')
    for name, _, part, thm in spec.statements:
        lines.append(f'Redirect "rocq.statement.{name}" Print {spec.modules[part]}.stmt_{name}.')
        if proofs:
            thm = thm or f"{ROCQ_PROOF}.{name}"
            lines.append(f'Redirect "rocq.proof.{name}" Check {thm}.')
            lines.append(f'Redirect "rocq.assumptions.{name}" Print Assumptions {thm}.')
    if proofs:
        lines.append('Redirect "rocq.reference" '
                     'Print Assumptions Compiler.transf_c_program_correct.')
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
    if t[0] == "lit":
        return t[2]
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
    for name, _ in spec.equations:
        forms[("equation", name)] = (spec_sort(spec.eqsorts[name]), name)
    for name, _, _, _ in spec.constants:
        sort, value = spec.values[name]
        forms[("constant", name)] = (spec_sort(sort), spec_canon(value, []))
    for name, _, _, _ in spec.statements:
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


def is_positive(t):
    return t == "BinNums.xH" or (isinstance(t, list) and len(t) == 2 and
                                 t[0] in ("BinNums.xO", "BinNums.xI"))


def rocq_string(t):
    """The characters of a Rocq string, a tree of String.String and Ascii.Ascii."""
    out = []
    while t not in ("String.EmptyString", "EmptyString"):
        if not (isinstance(t, list) and len(t) == 3 and t[0] in ("String.String", "String")):
            raise SpecError(f"not a string literal: {show(t)}")
        c = t[1]
        if not (isinstance(c, list) and len(c) == 9 and c[0] in ("Ascii.Ascii", "Ascii")
                and all(b in ("true", "false") for b in c[1:])):
            raise SpecError(f"not a character literal: {show(c)}")
        out.append(chr(sum(1 << i for i, b in enumerate(c[1:]) if b == "true")))
        t = t[2]
    s = '"' + "".join(out) + '"'
    if not is_str(s):
        raise SpecError(f"the string {s} has characters outside the language")
    return s


def heads_of(table_items):
    """The names that are applications, longest first, with their neutral symbols."""
    heads = [(n, name) for name, n in table_items if not isinstance(n, str)]
    return sorted(heads, key=lambda h: -len(h[0]))


def match_head(t, heads, term):
    """The neutral form of the application t when its head is a fixed application of heads."""
    for head, name in heads:
        if t[:len(head)] == head:
            return name if len(t) == len(head) else [name] + [term(a) for a in t[len(head):]]
    return None


class RocqNorm:
    def __init__(self, spec):
        self.table = {}
        items = [(name, names["rocq"]) for name, names in
                 list(spec.sorts.items()) + list(spec.symbols.items())]
        for name, n in items:
            if isinstance(n, str):
                self.table[n] = name
        self.heads = heads_of(items)
        for name in spec.rel_names:
            self.table[f"{ROCQ_SPEC}.{name}"] = name
        for name, _, part, _ in spec.statements:
            self.table[f"{spec.modules[part]}.stmt_{name}"] = "stmt_" + name
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
            if name == "BinNums.xH":
                return "1"
            if name in ("nil", "EmptyString", "String.EmptyString"):
                return {"nil": "?nil"}.get(name, '""')
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
        if is_positive(t):
            return str(positive(t))
        if name in ("String.String", "String"):
            return rocq_string(t)
        if name == "eq" and len(t) == 4:
            return ["=", self.term(t[2], scope), self.term(t[3], scope)]
        if name == "Some" and len(t) == 3:
            return ["Some", self.term(t[2], scope)]
        if name == "None" and len(t) == 2:
            return "None"
        if name == "nil" and len(t) == 2:
            return "nil"
        if name == "cons" and len(t) == 4:
            return ["cons", self.term(t[2], scope), self.term(t[3], scope)]
        if name == "pair" and len(t) == 5:
            return ["pair", self.term(t[3], scope), self.term(t[4], scope)]
        if name == "ex" and len(t) == 3 and isinstance(t[2], list) and t[2][0] == "fun" \
                and len(t[2][1]) == 1:
            return binder("exists", t[2][1], t[2][2], scope, self.sort, self.term)
        if name in ("and", "or", "iff", "not"):
            return [name] + [self.term(a, scope) for a in t[1:]]
        if name in ("option", "prod", "list"):
            return [name] + [self.term(a, scope) for a in t[1:]]
        stripped = [name] + t[1:] if name else t
        m = match_head(stripped, self.heads, lambda a: self.term(a, scope))
        if m is not None:
            return m
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


def rocq_print_output(text):
    """NAME, VALUE, and TYPE of the output 'NAME = VALUE\\n : TYPE' of Print."""
    m = re.fullmatch(r"(\S+) =\s+(.*)\n\s+: ([^\n]*?)\s*", text, re.S)
    if not m:
        raise SpecError(f"unexpected Print output: {text[:200]}")
    return m.group(1), m.group(2), m.group(3)


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
    for name, _ in spec.equations:
        text = rocq_file(d, f"rocq.equation.{name}")
        if text is not None:
            n, value, ty = rocq_print_output(text)
            if n != f"{ROCQ_SPEC}.eqn_{name}":
                notes[("equation", name)] = f"unexpected Print output: {text[:200]}"
            else:
                got[("equation", name)] = (term(ty), term(value))
    for name, _, _, part in spec.constants:
        text = rocq_file(d, f"rocq.constant.{name}")
        if text is not None:
            n, value, ty = rocq_print_output(text)
            if n != f"{spec.modules[part]}.cst_{name}":
                notes[("constant", name)] = f"unexpected Print output: {text[:200]}"
            else:
                got[("constant", name)] = (term(ty), term(value))
    for name, _, part, thm in spec.statements:
        text = rocq_file(d, f"rocq.statement.{name}")
        if text is not None:
            n, value, ty = rocq_print_output(text)
            if n != f"{spec.modules[part]}.stmt_{name}" or ty != "Prop":
                notes[("statement", name)] = f"unexpected Print output: {text[:200]}"
            else:
                got[("statement", name)] = term(value)
        if proofs:
            text = rocq_file(d, f"rocq.proof.{name}")
            if text is not None:
                n, ty = rocq_check_output(text)
                if n != (thm or f"{ROCQ_PROOF}.{name}"):
                    got[("proof", name)] = "?" + n
                elif thm is None:
                    got[("proof", name)] = term(ty)
                else:
                    hyp = f"{spec.modules[part]}.stmt_{name}"
                    got[("proof", name)] = ("stmt_" + name if first_premise(ty) == hyp
                                            else "a theorem whose first premise is not " + hyp)
            text = rocq_file(d, f"rocq.assumptions.{name}")
            if text is not None:
                got[("assumptions", name)] = assumption_names(text)
    if proofs:
        ref = rocq_file(d, "rocq.reference")
        got["reference"] = assumption_names(ref) if ref is not None else None
    return got, notes


def first_premise(ty):
    """The first premise of the Rocq type ty, when it is a product whose first variable the
    rest does not use."""
    t = RocqParser(ty).whole()
    if isinstance(t, list) and t[0] == "->":
        return t[1]
    if isinstance(t, list) and t[0] == "forall":
        (x, s), rest = t[1][0], t[1][1:]
        if x == "_" or not uses([t[0], rest, t[2]] if rest else t[2], x):
            return s
    return None


def assumption_names(text):
    return {m.group(1) for m in re.finditer(r"^([A-Za-z][A-Za-z0-9_.']*)( :|$)", text, re.M)}


# Lean: the S-expressions that ClightN.Read.dump writes, with every argument explicit.

class LeanNorm:
    def __init__(self, spec):
        self.table = {}
        items = [(name, names["lean"]) for name, names in
                 list(spec.sorts.items()) + list(spec.symbols.items())]
        for name, n in items:
            if isinstance(n, str):
                self.table[n] = name
        self.heads = heads_of(items)
        for name in spec.rel_names:
            self.table[f"{LEAN_SPEC}.{name}"] = name
        for name, _, _, _ in spec.statements:
            self.table[f"{LEAN_SPEC}.stmt_{name}"] = "stmt_" + name
        self.table["Prop"] = "Prop"

    def sort(self, s, scope):
        return self.term(s, scope)

    def term(self, t, scope):
        if isinstance(t, str):
            level = lookup(scope, t)
            if level:
                return level
            if is_str(t):
                return t
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
        if h == "OfNat.ofNat" and len(t) == 4 and t[1] in ("Nat", "LClight.ident") \
                and t[2][0] == "lit" and t[3] == ["instOfNatNat", t[2]]:
            return t[2][1]
        if h == "Eq" and len(t) == 4:
            return ["=", self.term(t[2], scope), self.term(t[3], scope)]
        if h == "Option.some" and len(t) == 3:
            return ["Some", self.term(t[2], scope)]
        if h == "Option.none" and len(t) == 2:
            return "None"
        if h == "List.nil" and len(t) == 2:
            return "nil"
        if h == "List.cons" and len(t) == 4:
            return ["cons", self.term(t[2], scope), self.term(t[3], scope)]
        if h == "Prod.mk" and len(t) == 5:
            return ["pair", self.term(t[3], scope), self.term(t[4], scope)]
        if h == "Exists" and len(t) == 3 and isinstance(t[2], list) and t[2][0] == "fun" \
                and len(t[2][1]) == 1:
            return binder("exists", [tuple(b) for b in t[2][1]], t[2][2], scope, self.sort,
                          self.term)
        conn = {"And": "and", "Or": "or", "Iff": "iff", "Not": "not", "Option": "option",
                "Prod": "prod", "List": "list"}
        if h in conn:
            return [conn[h]] + [self.term(a, scope) for a in t[1:]]
        m = match_head(t, self.heads, lambda a: self.term(a, scope))
        if m is not None:
            return m
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
        elif kind == "equation":
            name = full.removeprefix(f"{LEAN_SPEC}.eqn_")
            got[("equation", name)] = (norm.term(d[3], []), norm.term(d[2], []))
            if name not in spec.eqsorts:
                notes[("equation", name)] = "is not in the specification"
        elif kind == "constant":
            name = full.removeprefix(f"{LEAN_SPEC}.cst_")
            got[("constant", name)] = (norm.term(d[3], []), norm.term(d[2], []))
            if name not in spec.values:
                notes[("constant", name)] = "is not in the specification"
        elif kind == "statement":
            name = full.removeprefix(f"{LEAN_SPEC}.stmt_")
            got[("statement", name)] = norm.term(d[2], [])
            if d[3] != "Prop":
                notes[("statement", name)] = f"has the type {show(d[3])}"
            if not any(s[0] == name for s in spec.statements):
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

# The assumption that the Rocq theorem of a carried statement may add to those of CompCert's
# transf_c_program_correct: CompCert's argument about behaviors, as in rocq/check.sh.
ROCQ_CARRIED_EXTRA = {"ClassicalEpsilon.constructive_indefinite_description"}


def check(spec, rocq_dir, lean_out, proofs=True, expect=None):
    want = spec_forms(spec)
    found = set()
    reports = []

    def differ(prover, kind, name, message):
        found.add(f"{prover}:{kind}:{name}")
        reports.append(f"clightn: {prover}'s {kind} {name} {message}")

    def brief(form):
        text = show(form) if not isinstance(form, tuple) else " : ".join(map(show, form))
        return text if len(text) <= 2000 else text[:2000] + " [cut]"

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
                       f"  spec: {brief(form)}\n  {prover}: {brief(got[key])}")
        if not proofs:
            continue
        allowed = LEAN_AXIOMS if prover == "Lean" else got.get("reference")
        if allowed is None:
            differ(prover, "reference", "transf_c_program_correct", "was not printed")
            allowed = set()
        for name, _, _, thm in spec.statements:
            if ("proof", name) in notes:
                continue
            if ("proof", name) not in got:
                differ(prover, "proof", name, "is missing")
            elif got[("proof", name)] != "stmt_" + name:
                differ(prover, "proof", name, f"proves {show(got[('proof', name)])}, "
                       f"not stmt_{name}")
            extra = got.get(("assumptions", name), set()) - allowed
            if thm and prover == "Rocq":
                extra -= ROCQ_CARRIED_EXTRA
            if extra:
                differ(prover, "proof", name, f"assumes {' '.join(sorted(extra))}")
    for r in reports:
        print(r)
    nctors = sum(len(r[3]) for r in spec.relations)
    ncarried = sum(1 for s in spec.statements if s[3])
    counts = (f"{len(spec.relations)} relations with {nctors} constructors, "
              f"{len(spec.constants)} constants, and {len(spec.statements)} statements")
    if expect is not None:
        if found == expect:
            print(f"clightn: the check found exactly the planted differences, {len(expect)}")
            return 0
        print(f"clightn: planted but not found: {' '.join(sorted(expect - found)) or 'none'}")
        print(f"clightn: found but not planted: {' '.join(sorted(found - expect)) or 'none'}")
        return 1
    if found:
        print(f"clightn: {counts}; {len(found)} differences")
        return 1
    if proofs and ncarried:
        print(f"clightn: {counts} agree in Rocq and Lean; Lean proves every statement, Rocq "
              f"proves every statement but {ncarried}, which a Rocq theorem takes as its premise, "
              "and each proof has the permitted assumptions")
    elif proofs:
        print(f"clightn: {counts} agree in Rocq and Lean; each statement is proved in both, with "
              "the permitted assumptions")
    else:
        print(f"clightn: {counts} agree in Rocq and Lean")
    if spec.equations:
        print(f"clightn: {len(spec.equations)} equations agree in Rocq and Lean in their constants "
              "and sorts, and the step between the provers assumes each: "
              + " ".join(name for name, _ in spec.equations))
    return 0


def equations(spec):
    """Prints each equation of spec with its sort and its meaning in each prover."""
    for name, _ in spec.equations:
        names = spec.symbols[name]
        print(f"clightn: assumes {name} : {show(spec_sort(spec.eqsorts[name]))}, "
              f"{show(names['rocq'])} in Rocq and {show(names['lean'])} in Lean")


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
        ("nx_out", "init Bool.false Bool.true", "init Bool.false Bool.false", "Lean:ctor:nx_out"),
        ("nx_seq1", "(@ClightN.Base.app t1 t2)", "(@ClightN.Base.app t2 t1)", "Lean:ctor:nx_seq1"),
        ("np_intro", "(@LClight.calling_convention.mk (@Option.none _) Bool.false Bool.false)",
         "(@LClight.calling_convention.mk (@Option.none _) Bool.true Bool.false)",
         "Lean:ctor:np_intro"),
        ("nv_word", "(18446744073709551616 : Int)) (8 : Int))",
         "(18446744073709551616 : Int)) (4 : Int))", "Lean:ctor:nv_word"),
        ("nv_byte", "(@LT.lt Int Int.instLTInt (@ClightN.Base.u64 k)",
         "(@LE.le Int Int.instLEInt (@ClightN.Base.u64 k)", "Lean:ctor:nv_byte"),
        ("vl_uchar", "(1 : Int) j", "(4 : Int) j", "Lean:ctor:vl_uchar"),
        ("nr_load", "(nreads s (@Nat.succ c) t)", "(nreads s c t)", "Lean:ctor:nr_load"),
        ("li_before", "(@LClight.statement.Ssequence pre init) body", "init body",
         "Lean:ctor:li_before"),
        ("nr_intro", "(Inv (@Nat.succ n) le2 gv2 mb2)", "(Inv n le2 gv2 mb2)",
         "Lean:ctor:nr_intro"),
        ("bo_add_d", "(@LClight.Float.add LClight.Archi.aarch64 x y)",
         "(@LClight.Float.sub LClight.Archi.aarch64 x y)", "Lean:ctor:bo_add_d"),
        ("bo_lt_f_1", "LClight.comparison.Clt", "LClight.comparison.Cle", "Lean:ctor:bo_lt_f_1"),
        ("gi_d", "(@ClightN.Base.r64 (0 : Int))", "(@ClightN.Base.r64 (1 : Int))",
         "Lean:ctor:gi_d"),
        ("nx_store_cellf32", "(@ClightN.Base.f32_bits f)",
         "(@ClightN.Base.f32_bits (@LClight.Float32.neg f))", "Lean:ctor:nx_store_cellf32"),
        ("eqn_fadd64", "LClight.Archi.aarch64", "LClight.Archi.x86_64", "Lean:equation:fadd64"),
    ],
    "rocq-spec": [
        ("bo_mul_ul", "BinInt.Z.mul", "BinInt.Z.add", "Rocq:ctor:bo_mul_ul"),
        ("bool_ok", "Inductive bool_ok", "CoInductive bool_ok", "Rocq:relation:bool_ok"),
        ("bv_ui_false", "  | bv_ui_false :",
         "  | bv_extra : (forall (x : Integers.Int.int), (bool_ok\n"
         "      (@Ctypes.Tint Ctypes.I32 Ctypes.Unsigned (@Ctypes.mk_attr false (@None _)))\n"
         "      (@Values.Vint x) true))\n  | bv_ui_false :", "Rocq:constructors:bool_ok"),
        ("nx_if_false", "(bool_ok ta v false)", "(bool_ok ta v true)", "Rocq:ctor:nx_if_false"),
        ("nx_loop", "(@NBase.app t1 (@NBase.app t2 t3))", "(@NBase.app (@NBase.app t1 t2) t3)",
         "Rocq:ctor:nx_loop"),
        ("in_there", "((in_defs rest x g) -> (in_defs (@cons _ d rest) x g))",
         "(in_defs (@cons _ d rest) x g)", "Rocq:ctor:in_there"),
        ("vl_uint", "(4)%Z j (@Values.Vint j)", "(8)%Z j (@Values.Vint j)", "Rocq:ctor:vl_uint"),
        ("ni_intro", "(@eq _ (mb x j) (0)%Z)", "(@eq _ (mb x j) (1)%Z)", "Rocq:ctor:ni_intro"),
        ("nx_vload", "(@NBase.rptr (@BinInt.Z.mul sz (@NBase.u64 k)))",
         "(@NBase.rptr (@NBase.u64 k))", "Rocq:ctor:nx_vload"),
        ("nr_store", "((nreads s c t) ->", "((nreads s (S c) t) ->", "Rocq:ctor:nr_store"),
        ("nr_intro", "(Inv O le gv mb)", "(Inv (S O) le gv mb)", "Rocq:ctor:nr_intro"),
        ("co_d_ul", "Floats.Float.to_longu", "Floats.Float.to_long", "Rocq:ctor:co_d_ul"),
        ("uo_abs_d", "(@Floats.Float.abs x)", "(@Floats.Float.neg x)", "Rocq:ctor:uo_abs_d"),
        ("nx_sqrt", '"__builtin_fsqrt"', '"__builtin_sqrt"', "Rocq:ctor:nx_sqrt"),
        ("eqn_fmul32", "Floats.Float32.mul", "Floats.Float32.div", "Rocq:equation:fmul32"),
    ],
    "lean-gcd": [
        ("cst_gcd_trace", "(21 : Int)", "(22 : Int)", "Lean:constant:gcd_trace"),
        ("cst_gcd_defs", "(1071 : Int)", "(1072 : Int)", "Lean:constant:gcd_defs"),
    ],
    "rocq-gcd": [
        ("cst_gcd_main", "(22880918)%positive", "(22880919)%positive", "Rocq:constant:gcd_main"),
        ("cst_gcd_defs", "(462)%Z", "(463)%Z", "Rocq:constant:gcd_defs"),
    ],
    "lean-sha": [
        ("cst_sha_defs", "(268435456 : Int)", "(268435448 : Int)", "Lean:constant:sha_defs"),
        ("stmt_sha_reads", "(nreads sigma Nat.zero t)", "(nreads sigma (@Nat.succ Nat.zero) t)",
         "Lean:statement:sha_reads"),
    ],
    "rocq-sha": [
        ("cst_sha_main", "(22880918)%positive", "(22880919)%positive", "Rocq:constant:sha_main"),
        ("cst_sha_defs", "(268435456)%Z", "(268435448)%Z", "Rocq:constant:sha_defs"),
    ],
    "lean-ctl": [
        ("cst_ctl_defs", "(4096 : Int)", "(4097 : Int)", "Lean:constant:ctl_defs"),
        ("stmt_ctl_reacts", "(@ClightN.Base.app (P sigma n) (W sigma n))",
         "(@ClightN.Base.app (W sigma n) (P sigma n))", "Lean:statement:ctl_reacts"),
    ],
    "rocq-ctl": [
        ("cst_ctl_main", "(22880918)%positive", "(22880919)%positive", "Rocq:constant:ctl_main"),
        ("stmt_ctl_reacts", "(@eq _ (P sigma O) (@nil _))", "(@eq _ (P sigma (@S O)) (@nil _))",
         "Rocq:statement:ctl_reacts"),
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
        ("div_f_f", "theorem div_f_f : stmt_div_f_f := by",
         "theorem div_f_f : stmt_div_f_f := by\n  sorry\n\n"
         "theorem div_f_f_unused : stmt_div_f_f := by", "Lean:proof:div_f_f"),
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
        ("ne_d_d", "Theorem ne_d_d : stmt_ne_d_d.\nProof.",
         "Theorem ne_d_d : stmt_ne_d_d.\nProof.\nAdmitted.\n\n"
         "Theorem ne_d_d_unused : stmt_ne_d_d.\nProof.", "Rocq:proof:ne_d_d"),
    ],
}

# The planted errors of each form of an instance's statement: the text of the Lean rendering and
# its replacement, then the text of the Rocq rendering and its replacement.
STATEMENT_PLANTS = {
    "terminates": ("(@ClightN.Base.r32 (0 : Int))", "(@ClightN.Base.r32 (2 : Int))",
                   "(@NBase.r32 (0)%Z)", "(@NBase.r32 (2)%Z)"),
    "reads": ("(nreads sigma Nat.zero t)", "(nreads sigma (@Nat.succ Nat.zero) t)",
              "(nreads sigma O t)", "(nreads sigma (S O) t)"),
    "reacts": ("(@ClightN.Base.app (P sigma n) (W sigma n))",
               "(@ClightN.Base.app (W sigma n) (P sigma n))",
               "(@eq _ (P sigma O) (@nil _))", "(@eq _ (P sigma (@S O)) (@nil _))"),
}


def instance_mutations(group, form):
    """The planted errors of the group lean-NAME, rocq-NAME, lean-NAME-proof, or rocq-NAME-proof
    of the instance NAME, whose statement NAME_FORM has the form FORM: in each prover's rendering
    a changed identifier of main and a changed statement, in the Lean proof sorry in place of the
    proof of the statement, and in the Rocq proof Admitted in place of the Qed of the theorem that
    takes the statement as its premise.  An edit whose OLD is None replaces the declaration's text
    after its first :=."""
    m = re.fullmatch(r"(lean|rocq)-(\w+?)(-proof)?", group)
    if not m or form not in STATEMENT_PLANTS:
        raise SpecError(f"{group}: no planted errors for the form {form}")
    prover, name, proof = m.groups()
    who = "Lean" if prover == "lean" else "Rocq"
    stmt = f"{name}_{form}"
    if proof:
        if prover == "lean":
            return [(stmt, None, " by\n  sorry\n", f"Lean:proof:{stmt}")]
        return [(f"{name}_asm", "Qed.", "Admitted.", f"Rocq:proof:{stmt}")]
    lean_old, lean_new, rocq_old, rocq_new = STATEMENT_PLANTS[form]
    if prover == "lean":
        main = ("(22880918 : LClight.ident)", "(22880919 : LClight.ident)")
        old, new = lean_old, lean_new
    else:
        main = ("(22880918)%positive", "(22880919)%positive")
        old, new = rocq_old, rocq_new
    return [(f"cst_{name}_main", *main, f"{who}:constant:{name}_main"),
            (f"stmt_{stmt}", old, new, f"{who}:statement:{stmt}")]


DECL_START = r"^(\s*\| {name} :|(def|theorem|inductive|Definition|Theorem|Inductive) {name}\b)"
DECL_NEXT = r"^(\s*\| \S+ :|(def|theorem|inductive|Definition|Theorem|Lemma|Inductive|end) |$)"


def mutate(group, src, out, form=None):
    """Writes SRC with the planted errors of GROUP to OUT, and prints the differences that the
    check must report.  A Lean file also imports the reader and calls it, unless it does."""
    text = open(src).read()
    keys = []
    plants = MUTATIONS[group] if group in MUTATIONS else instance_mutations(group, form)
    for decl, old, new, key in plants:
        m = re.search(DECL_START.format(name=re.escape(decl)), text, re.M)
        if not m:
            raise SpecError(f"{group}: no declaration {decl}")
        rest = text[m.end():]
        n = re.search(DECL_NEXT, rest, re.M)
        end = m.end() + (n.start() if n else len(rest))
        block = text[m.start():end]
        if old is None:
            if ":=" not in block:
                raise SpecError(f"{group}: {decl} has no :=")
            planted = block[:block.index(":=") + 2] + new
        elif block.count(old) != 1:
            raise SpecError(f"{group}: {decl} holds the text to replace {block.count(old)} times")
        else:
            planted = block.replace(old, new)
        text = text[:m.start()] + planted + text[end:]
        keys.append(key)
    if group.startswith("lean") and "run_cmd ClightN.Read.dump" not in text:
        lines = text.split("\n")
        last = max(i for i, l in enumerate(lines) if l.startswith("import "))
        lines.insert(last + 1, "import LeanExe.Native.ClightN.Read")
        text = "\n".join(lines) + "\nrun_cmd ClightN.Read.dump\n"
    open(out, "w").write(text)
    print(",".join(keys))


def specs(arg):
    return Spec(arg.split(","))


def run(argv):
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
            render(specs(args[0]), args[1].split(","), args[2].split(","))
        elif cmd == "rocq-reader" and len(args) == 2:
            rocq_reader(specs(args[0]), args[1], "--no-proofs" not in flags)
        elif cmd == "check" and len(args) == 3:
            return check(specs(args[0]), args[1], args[2], "--no-proofs" not in flags, expect)
        elif cmd == "mutate" and len(args) in (3, 4):
            mutate(*args)
        elif cmd == "equations" and len(args) == 1:
            equations(specs(args[0]))
        else:
            print(__doc__, file=sys.stderr)
            return 2
    except SpecError as e:
        print(f"clightn: {e}", file=sys.stderr)
        return 1
    return 0


def main(argv):
    """Runs the command on a thread with a large stack, since the terms of a program literal nest
    deeply."""
    sys.setrecursionlimit(1000000)
    threading.stack_size(1 << 29)
    result = []
    t = threading.Thread(target=lambda: result.append(run(argv)))
    t.start()
    t.join()
    return result[0] if result else 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
