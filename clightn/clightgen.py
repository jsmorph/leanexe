# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
"""Writes the program of a Coq file that clightgen printed for a bare-metal program, and a
statement of its runs, in the neutral language of clightn/N.nsx (clightn/README.md).

  uv run clightn/clightgen.py FILE.v OUT.nsx NAME MODULE THEOREM terminates BYTES RESULT
  uv run clightn/clightgen.py FILE.v OUT.nsx NAME MODULE THEOREM reads
  uv run clightn/clightgen.py FILE.v OUT.nsx NAME MODULE THEOREM reacts

writes the part MODULE with the constants NAME_defs and NAME_main, the definitions of the file's
program and the identifier of its main, and a statement that the Rocq theorem THEOREM takes as its
premise.  With terminates, the part also holds the constant NAME_trace, the trace of one volatile
store to lx_out of each byte of BYTES, a list separated by commas, and the statement
NAME_terminates says that the program terminates with that trace and the result RESULT.  With
reads, the statement NAME_reads says that for every sequence sigma of the values of its volatile
loads the program terminates with a trace whose k-th volatile load reads sigma k.  With reacts,
the statement NAME_reacts says that there are functions W and P of the sequence sigma such that,
for every sigma, main runs forever with no event before its loop and the trace W sigma n in
iteration n, P sigma n is the trace of the first n iterations, and its k-th volatile load reads
sigma k.  The script is untrusted: Rocq proves that the constant is the program of the file, and
the check compares what each prover elaborated with the output of this script.
"""
import re
import sys

TOKEN = re.compile(r'\(\*|\*\)|\{\||\|\}|:=|::|"[^"]*"|-?\d+|[A-Za-z_][A-Za-z0-9_\']*'
                   r'(?:\.[A-Za-z_][A-Za-z0-9_\']*)*|\.(?=\s|$)|[()$%,;:]', re.M)


class Error(Exception):
    pass


def tokens(text):
    out, depth = [], 0
    for m in TOKEN.finditer(text):
        t = m.group(0)
        if t == "(*":
            depth += 1
        elif t == "*)":
            depth -= 1
        elif depth == 0:
            out.append(t)
    return out


def sentences(toks):
    """The definitions of the file: name and the tokens of the term, outside module Info."""
    defs, cur, skip = {}, [], False
    for t in toks:
        if t != ".":
            cur.append(t)
            continue
        if cur[:1] == ["Module"]:
            skip = True
        elif cur[:1] == ["End"]:
            skip = False
        elif cur[:1] == ["Definition"] and not skip:
            i = cur.index(":=")
            defs[cur[1]] = cur[i + 1:]
        cur = []
    return defs


class Parser:
    """Terms as clightgen prints them: applications, :: lists, pairs, records, $"name",
    numerals with a scope, and strings."""

    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else None

    def eat(self, x=None):
        tok = self.peek()
        if tok is None or (x is not None and tok != x):
            raise Error(f"expected {x}, found {tok}")
        self.i += 1
        return tok

    def term(self):
        left = self.app()
        if self.peek() == "::":
            self.eat()
            return ["cons", left, self.term()]
        return left

    def app(self):
        items = []
        while self.peek() not in (None, ")", ",", ";", "|}", "::"):
            items.append(self.atom())
        if not items:
            raise Error("an empty application")
        return items[0] if len(items) == 1 else ["app"] + items

    def atom(self):
        tok = self.eat()
        if tok == "(":
            first = self.term()
            if self.peek() == ",":
                self.eat()
                second = self.term()
                self.eat(")")
                return ["pair", first, second]
            self.eat(")")
            return first
        if tok == "{|":
            fields = []
            while True:
                name = self.eat()
                self.eat(":=")
                fields.append((name, self.term()))
                if self.peek() == ";":
                    self.eat()
                    continue
                self.eat("|}")
                return ["record", fields]
        if tok == "$":
            return ["ident_of_string", self.eat()]
        if self.peek() == "%":
            self.eat()
            scope = self.eat()
            return ["scoped", tok, scope]
        return tok


def ident_of_string(s):
    """ident_of_string of export/Ctypesdefs.v: six bits for each character, the first character
    in the lowest bits."""
    p = 1
    for c in reversed(s):
        if c.isdigit():
            code = ord(c) - ord("0")
        elif "a" <= c <= "z":
            code = 10 + ord(c) - ord("a")
        elif "A" <= c <= "Z":
            code = 36 + ord(c) - ord("A")
        elif c == "_":
            code = 62
        else:
            raise Error(f"the character {c!r} in {s}")
        p = p * 64 + code
    return p


NOATTR = "(mk_attr false None)"
VATTR = "(mk_attr true None)"
TYPES = {"tvoid": "Tvoid", "tschar": f"(Tint I8 Signed {NOATTR})",
         "tuchar": f"(Tint I8 Unsigned {NOATTR})", "tshort": f"(Tint I16 Signed {NOATTR})",
         "tushort": f"(Tint I16 Unsigned {NOATTR})", "tint": f"(Tint I32 Signed {NOATTR})",
         "tuint": f"(Tint I32 Unsigned {NOATTR})", "tbool": f"(Tint IBool Unsigned {NOATTR})",
         "tlong": f"(Tlong Signed {NOATTR})", "tulong": f"(Tlong Unsigned {NOATTR})",
         "tfloat": f"(Tfloat F32 {NOATTR})", "tdouble": f"(Tfloat F64 {NOATTR})"}
DATA = {"Sskip", "Sbreak", "Scontinue", "Sassign", "Sset", "Scall", "Sbuiltin", "Ssequence",
        "Sifthenelse", "Sloop", "Sreturn", "Econst_int", "Econst_float", "Econst_single",
        "Econst_long", "Evar", "Etempvar", "Ederef", "Eaddrof", "Eunop", "Ebinop", "Ecast",
        "Onotbool", "Onotint", "Oneg", "Oabsfloat", "Oadd", "Osub", "Omul", "Odiv", "Omod",
        "Oand", "Oor", "Oxor", "Oshl", "Oshr", "Oeq", "One", "Olt", "Ogt", "Ole", "Oge",
        "Some", "None", "nil", "true", "false", "Gfun", "Gvar", "Internal", "External",
        "Init_int8", "Init_int16", "Init_int32", "Init_int64", "Init_float32", "Init_float64",
        "Init_space", "EF_external", "EF_builtin", "EF_runtime", "EF_vload", "EF_vstore",
        "mksignature", "Tfunction", "Mbool", "Mint8signed", "Mint8unsigned", "Mint16signed",
        "Mint16unsigned", "Mint32", "Mint64", "Mfloat32", "Mfloat64", "Many32", "Many64"}
RECORDS = {
    ("gvar_info", "gvar_init", "gvar_readonly", "gvar_volatile"): "mkglobvar",
    ("fn_return", "fn_callconv", "fn_params", "fn_vars", "fn_temps", "fn_body"): "mkfunction",
    ("cc_vararg", "cc_unproto", "cc_structret"): "mkcallconv"}


class Converter:
    def __init__(self, defs):
        self.defs = defs
        self.idents = {}
        for name, toks in defs.items():
            if name.startswith("_"):
                t = Parser(toks).term()
                if isinstance(t, list) and t[0] == "ident_of_string":
                    self.idents[name] = ident_of_string(t[1].strip('"'))
                elif isinstance(t, list) and t[0] == "scoped" and t[2] == "positive":
                    self.idents[name] = int(t[1])
                else:
                    raise Error(f"the identifier {name}")

    def ident(self, name):
        return f"(lit ident {self.idents[name]})"

    def num(self, tok):
        n = int(tok)
        return str(n) if n >= 0 else f"(- 0 {-n})"

    def conv(self, t):
        if isinstance(t, str):
            if t in self.idents:
                return self.ident(t)
            if re.fullmatch(r"-?\d+", t):
                return self.num(t)
            if t.startswith('"'):
                return t
            if t in TYPES:
                return TYPES[t]
            if t == "cc_default":
                return "(cc_default)"
            if t.startswith("AST.X") or t in DATA:
                return t.removeprefix("AST.")
            if t in self.defs and (t.startswith("v_") or t.startswith("f_")):
                return self.conv(Parser(self.defs[t]).term())
            raise Error(f"the name {t}")
        h = t[0]
        if h == "cons":
            return f"(cons {self.conv(t[1])} {self.conv(t[2])})"
        if h == "pair":
            return f"(pair {self.conv(t[1])} {self.conv(t[2])})"
        if h == "record":
            names = tuple(n for n, _ in t[1])
            if names not in RECORDS:
                raise Error(f"the record {names}")
            return f"({RECORDS[names]} " + " ".join(self.conv(v) for _, v in t[1]) + ")"
        if h == "scoped":
            raise Error(f"the numeral {t[1]}%{t[2]}")
        args = t[1:]
        f = args[0]
        rest = args[1:]
        if f == "Int.repr":
            return f"(r32 {self.conv(rest[0])})"
        if f == "Int64.repr":
            return f"(r64 {self.conv(rest[0])})"
        if f == "Float.of_bits":
            return f"(f64_of_bits {self.conv(rest[0])})"
        if f == "Float32.of_bits":
            return f"(f32_of_bits {self.conv(rest[0])})"
        if f == "tptr":
            return f"(Tpointer {self.conv(rest[0])} {NOATTR})"
        if f == "tarray":
            return f"(Tarray {self.conv(rest[0])} {self.conv(rest[1])} {NOATTR})"
        if f == "tvolatile":
            inner = self.conv(rest[0])
            if NOATTR not in inner or not inner.endswith(NOATTR + ")"):
                raise Error(f"the volatile type {inner}")
            return inner[: -len(NOATTR) - 1] + VATTR + ")"
        if f == "Swhile":
            c, s = self.conv(rest[0]), self.conv(rest[1])
            return f"(Sloop (Ssequence (Sifthenelse {c} Sskip Sbreak) {s}) Sskip)"
        if isinstance(f, str) and (f in DATA or f.startswith("AST.")):
            return "(" + " ".join([f.removeprefix("AST.")] + [self.conv(a) for a in rest]) + ")"
        raise Error(f"the application of {f}")


def main(argv):
    form = argv[6] if len(argv) > 6 else None
    if not ((form == "terminates" and len(argv) == 9) or
            (form in ("reads", "reacts") and len(argv) == 7)):
        print(__doc__, file=sys.stderr)
        return 2
    src, out, name, module, theorem = argv[1:6]
    sys.setrecursionlimit(100000)
    try:
        defs = sentences(tokens(open(src).read()))
        c = Converter(defs)
        if defs.get("composites") != ["nil"]:
            raise Error("the program has composite types")
        prog = Parser(defs["prog"]).term()
        if not (isinstance(prog, list) and prog[1:5] == ["mkprogram", "composites",
                                                          "global_definitions", "public_idents"]):
            raise Error("the program is not mkprogram of the file's definitions")
        main_id = c.ident(prog[5])
        program = c.conv(Parser(defs["global_definitions"]).term())
        if form == "terminates":
            out_id = c.ident("_lx_out")
            trace = "nil"
            for b in reversed([int(x) for x in argv[7].split(",")]):
                trace = f"(cons (Event_vstore Mint32 {out_id} (rptr 0) (EVint (r32 {b}))) {trace})"
    except (Error, KeyError) as e:
        print(f"clightgen.py: {e}", file=sys.stderr)
        return 1
    text = [f"; Generated by clightn/clightgen.py from {src.rsplit('/', 1)[-1]}.  Do not edit.",
            f"(part (rocq {module}))",
            f"(constant {name}_defs (dlist)",
            "  " + program + ")",
            f"(constant {name}_main ident {main_id})"]
    if form == "terminates":
        text += [f"(constant {name}_trace (list event)",
                 "  " + trace + ")",
                 f"(carried {name}_terminates (rocq {theorem})",
                 f"  (nprog {name}_defs {name}_main {name}_trace (r32 {argv[8]})))"]
    elif form == "reads":
        text += [f"(carried {name}_reads (rocq {theorem})",
                 "  (forall ((sigma (-> nat w32))) (exists ((t (list event)) (r w32))",
                 f"    (and (nprog {name}_defs {name}_main t r) (nreads sigma O t)))))"]
    else:
        text += [f"(carried {name}_reacts (rocq {theorem})",
                 "  (exists ((W (-> (-> nat w32) (-> nat (list event))))",
                 "           (P (-> (-> nat w32) (-> nat (list event)))))",
                 "    (forall ((sigma (-> nat w32)))",
                 f"      (and (nreacts {name}_defs {name}_main nil (W sigma))",
                 "        (and (= (P sigma O) nil)",
                 "          (and (forall ((n nat))",
                 "                 (= (P sigma (S n)) (app (P sigma n) (W sigma n))))",
                 "            (forall ((n nat)) (nreads sigma O (P sigma n)))))))))"]
    open(out, "w").write("\n".join(text) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv))
