import LeanExe.Native.CText

/-!
The `main` of a bare-metal program and the declaration of `lx_out` (`docs/native-bare-metal.md`).
`main` calls `lx_init`, then the entry `k` of the translation on constant arguments of type
`unsigned long long`, returns `lx_status` when it is not 0, and otherwise writes the result's
bytes to `lx_out`, one volatile store of `unsigned int` per byte, and returns 0.  A result of
the kind `word` is a `UInt64`, written as its eight bytes from the lowest; a result of the kind
`array` is the address of an `Array UInt64` in `lx_mem`, written as its length word and its
elements, the `8 n + 8` bytes from the address in the order of memory.

The statements have the forms that `clightgen` gives the C text of `cmain`, as its Coq output
prints them: a C block nests its statements to the right, a call `l0 = f(args);` becomes
`Scall (Some t) f args` followed by `Sset l0 (Etempvar t)`, a store `lx_out = e;` becomes
`Sbuiltin None (EF_vstore Mint32)` of the address of `lx_out` and `e` (`cfrontend/SimplExpr.v`,
lines 219 to 226), a `while` loop is `Swhile` (`cfrontend/Clight.v`, lines 119 and 120), and
`clightgen` appends `return 0;` to the body of `main`.  The per-build check compares the
program that `clightgen` reads with these definitions.
-/

namespace LeanExe.Native

open LClight

/-- The identifier of `lx_out`. -/
def outId : ident := 28

/-- `volatile unsigned int`, which `clightgen` prints as `tvolatile tuint`
(`export/Ctypesdefs.v`, lines 30, 39, and 41 to 54). -/
def outType : type := .Tint .I32 .Unsigned { attr_volatile := true, attr_alignas := none }

/-- `extern volatile unsigned int lx_out;`. -/
def outVar : globvar type :=
  { gvar_info := outType, gvar_init := [], gvar_readonly := false, gvar_volatile := true }

/-- The definitions after the translation's in a bare-metal program: `lx_out` and `main`. -/
def bareTail (main : function) : List (ident × globdef (fundef function) type) :=
  [(outId, .Gvar outVar), (mainId, .Gfun (.Internal main))]

/-- The kinds of result that `main` writes. -/
inductive OutKind where
  | word
  | array
  deriving Repr, DecidableEq

/-- `main`'s temporaries: the result `l0`, the number of bytes `l1`, the index `l2`, and the
temporary of the call. -/
def resTemp : ident := localId 0
def lenTemp : ident := localId 1
def idxTemp : ident := localId 2
def callTemp : ident := callId 0

/-- `lx_out = (unsigned int) e;`. -/
def outStore (e : expr) : statement :=
  .Sbuiltin none (.EF_vstore .Mint32) [.Tpointer outType noattr, outType]
    [.Eaddrof (.Evar outId outType) (.Tpointer outType noattr), .Ecast e tuint]

/-- `lx_init();`. -/
def initCall : statement := .Scall none (.Evar initId (.Tfunction [] .Tvoid cc_default)) []

/-- `l0 = lxf_k(args);`. -/
def entryCall (k : Nat) (args : List UInt64) : statement :=
  .Ssequence
    (.Scall (some callTemp) (.Evar (funId k) (.Tfunction (args.map fun _ => tulong) tulong cc_default))
      (args.map fun a => .Econst_long a tulong))
    (.Sset resTemp (.Etempvar callTemp tulong))

/-- `if (lx_status != 0U) return (int) lx_status;`. -/
def statusTest : statement :=
  .Sifthenelse (.Ebinop .One (.Evar statusId tuint) (.Econst_int 0 tuint) tint)
    (.Sreturn (some (.Ecast (.Evar statusId tuint) tint))) .Sskip

/-- `lx_out = (unsigned int) (l0 >> 8 j & 255ULL);`: byte `j` of a word. -/
def wordOut (j : Nat) : statement :=
  outStore (.Ebinop .Oand (.Ebinop .Oshr (.Etempvar resTemp tulong) (clong (8 * j)) tulong)
    (clong 255) tulong)

/-- The loop that writes the bytes from `l0` to `l0 + l1`:
`while (l2 < l1) { lx_out = (unsigned int) ((unsigned char *) lx_mem)[l0 + l2]; l2 = l2 + 1ULL; }`. -/
def bytesLoop (cap : Nat) : statement :=
  .Sloop
    (.Ssequence
      (.Sifthenelse (.Ebinop .Olt (.Etempvar idxTemp tulong) (.Etempvar lenTemp tulong) tint)
        .Sskip .Sbreak)
      (.Ssequence
        (outStore (byteAt cap (.Ebinop .Oadd (.Etempvar resTemp tulong) (.Etempvar idxTemp tulong)
          tulong)))
        (.Sset idxTemp (.Ebinop .Oadd (.Etempvar idxTemp tulong) (clong 1) tulong))))
    .Sskip

/-- The statements that write the result. -/
def outStmts (cap : Nat) : OutKind → List statement
  | .word => (List.range 8).map wordOut
  | .array =>
      [.Sset lenTemp (loadBytes cap resTemp 7),
        .Sset lenTemp (.Ebinop .Oadd (.Ebinop .Omul (clong 8) (.Etempvar lenTemp tulong) tulong)
          (clong 8) tulong),
        .Sset idxTemp (clong 0),
        bytesLoop cap]

/-- The body of `main` before the `return 0;` that `clightgen` appends. -/
def mainBody (cap k : Nat) (args : List UInt64) (kind : OutKind) : statement :=
  seqList ([initCall, entryCall k args, statusTest] ++ outStmts cap kind)

def mainTemps : OutKind → List (ident × type)
  | .word => [(resTemp, tulong), (callTemp, tulong)]
  | .array => [(resTemp, tulong), (lenTemp, tulong), (idxTemp, tulong), (callTemp, tulong)]

/-- `main`, which calls the entry `k` on `args` and writes its result of the kind `kind`. -/
def bareMain (cap k : Nat) (args : List UInt64) (kind : OutKind) : function :=
  { fn_return := tint, fn_callconv := cc_default, fn_params := [], fn_vars := [],
    fn_temps := mainTemps kind,
    fn_body := .Ssequence (mainBody cap k args kind) (.Sreturn (some (.Econst_int 0 tint))) }

section

variable (gname : ident → String) (tname : ident → String) (isCall : ident → Bool)

/-- The C text of `lx_out`'s declaration and of `main`, without the `return 0;` that `clightgen`
appends, to follow the C text of the translation. -/
def cmain (cap k : Nat) (args : List UInt64) (kind : OutKind) : Except String String := do
  let decls ← ((mainTemps kind).filter fun (t, _) => !isCall t).mapM fun (t, ty) => do
    pure s!"  {← ctype ty} {tname t};\n"
  pure ("extern volatile unsigned int lx_out;\n" ++ "int main(void) {\n" ++ String.join decls ++
    (← cstmt gname tname isCall 1 (mainBody cap k args kind)) ++ "}\n")

end

/-- The bytes of a word, from the lowest. -/
def encodeWord (x : UInt64) : List UInt8 :=
  (List.range 8).map fun j => (x >>> UInt64.ofNat (8 * j)).toUInt8

/-- The bytes of an array of words in memory: its length word, then its elements. -/
def encodeArray (xs : Array UInt64) : List UInt8 :=
  encodeWord (UInt64.ofNat xs.size) ++ xs.toList.flatMap encodeWord

/-- The trace of `main`'s output: one store of `unsigned int` to `lx_out` per byte. -/
def outTrace (bs : List UInt8) : trace :=
  bs.map fun b => .Event_vstore .Mint32 outId Ptrofs.zero (.EVint (UInt32.ofNat b.toNat))

/-- The C text of the bare-metal program of the translation `t`: the translation's text, then
`lx_out` and `main`. -/
def Translation.bareText (t : Translation) (cap k : Nat) (args : List UInt64) (kind : OutKind) :
    Except String String := do
  let gname (id : ident) : String := if id == outId then "lx_out" else t.gname id
  pure ((← t.text) ++ (← cmain gname tempName isCallTemp cap k args kind))

end LeanExe.Native
