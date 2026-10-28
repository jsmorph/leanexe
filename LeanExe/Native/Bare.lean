import LeanExe.Native.CText

/-!
The `main` of a bare-metal program and the declaration of `lx_out` (`docs/native-bare-metal.md`).
`main` calls `lx_init`, then the entry `k` of the translation on constant arguments of type
`unsigned long long`, returns `lx_status` when it is not 0, and otherwise writes the result's
bytes to `lx_out`, one volatile store of `unsigned int` per byte, and returns 0.  A result of
the kind `word` is a `UInt64`, written as its eight bytes from the lowest; a result of the kind
`array` is the address of an `Array UInt64` in `lx_mem`, written as its length word and its
elements, the `8 n + 8` bytes from the address in the order of memory.  A result of the kind
`words k` is the `k` words that an entry with `k` results leaves in the result globals, written
in order, each from the lowest byte; the call of such an entry has no result.

The `main` of a program with input, `inMain`, reads its input from `lx_in`, the bytes that a
loader places at a fixed address: a length `n` of eight bytes, the lowest first, and then `n`
bytes, each read with a volatile load of `unsigned char`.  It returns 64 when `n` exceeds
`inMax`.  Otherwise it allocates an array of `⌈n / 8⌉` words through the module's `alloc`,
function 0, returns `lx_status` when the allocation sets it, stores the number of words and the
`n` bytes into the array, and calls the entry on the array's address and `n`.  It then tests
`lx_status` and writes the result as `main` does.

The statements have the forms that `clightgen` gives the C text of `cmain` and `cinMain`, as its
Coq output prints them: a C block nests its statements to the right, a call `l0 = f(args);`
becomes `Scall (Some t) f args` followed by `Sset l0 (Etempvar t)`, a store `lx_out = e;`
becomes `Sbuiltin None (EF_vstore Mint32)` of the address of `lx_out` and `e`, and a load
`l6 = lx_in[e];` becomes `Sbuiltin (Some t) (EF_vload Mint8unsigned)` of the address of the
element followed by `Sset l6 (Ecast (Etempvar t) tulong)` (`cfrontend/SimplExpr.v`, lines 199 to
226).  A `while` loop is `Swhile` (`cfrontend/Clight.v`, lines 119 and 120), and `clightgen`
appends `return 0;` to the body of `main`.  `clightgen` lists the temporaries that it creates
after the declared ones, the last created first.  The per-build check compares the program that
`clightgen` reads with these definitions.
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
  | words (k : Nat)
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

/-- `l0 = lxf_k(args);`, through the call temporary `t`, for an entry of the parameter types
`tys`. -/
def resultCall (t : ident) (k : Nat) (tys : List type) (args : List expr) : statement :=
  .Ssequence (.Scall (some t) (.Evar (funId k) (.Tfunction tys tulong cc_default)) args)
    (.Sset resTemp (.Etempvar t tulong))

/-- `lxf_k(args);`, for an entry of the parameter types `tys` that returns `void`. -/
def voidCall (k : Nat) (tys : List type) (args : List expr) : statement :=
  .Scall none (.Evar (funId k) (.Tfunction tys .Tvoid cc_default)) args

/-- `l0 = lxf_k(args);`. -/
def entryCall (k : Nat) (args : List UInt64) : statement :=
  resultCall callTemp k (args.map fun _ => tulong) (args.map fun a => .Econst_long a tulong)

/-- The call of the entry on constant arguments: `lxf_k(args);` for the kind `words`, and
`entryCall` otherwise. -/
def entryStmt (kind : OutKind) (k : Nat) (args : List UInt64) : statement :=
  match kind with
  | .words _ => voidCall k (args.map fun _ => tulong) (args.map fun a => .Econst_long a tulong)
  | _ => entryCall k args

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

/-- `lx_out = (unsigned int) (lx_r<i>_l >> 8 j & 255ULL);`: byte `j` of the result global `i`. -/
def globalOut (i j : Nat) : statement :=
  outStore (.Ebinop .Oand (.Ebinop .Oshr (.Evar (resId i .i64) tulong) (clong (8 * j)) tulong)
    (clong 255) tulong)

/-- The statements that write the result. -/
def outStmts (cap : Nat) : OutKind → List statement
  | .word => (List.range 8).map wordOut
  | .words k => (List.range k).flatMap fun i => (List.range 8).map (globalOut i)
  | .array =>
      [.Sset lenTemp (loadBytes cap resTemp 7),
        .Sset lenTemp (.Ebinop .Oadd (.Ebinop .Omul (clong 8) (.Etempvar lenTemp tulong) tulong)
          (clong 8) tulong),
        .Sset idxTemp (clong 0),
        bytesLoop cap]

/-- The body of `main` before the `return 0;` that `clightgen` appends. -/
def mainBody (cap k : Nat) (args : List UInt64) (kind : OutKind) : statement :=
  seqList ([initCall, entryStmt kind k args, statusTest] ++ outStmts cap kind)

def mainTemps : OutKind → List (ident × type)
  | .word => [(resTemp, tulong), (callTemp, tulong)]
  | .array => [(resTemp, tulong), (lenTemp, tulong), (idxTemp, tulong), (callTemp, tulong)]
  | .words _ => []

/-- `main`, which calls the entry `k` on `args` and writes its result of the kind `kind`. -/
def bareMain (cap k : Nat) (args : List UInt64) (kind : OutKind) : function :=
  { fn_return := tint, fn_callconv := cc_default, fn_params := [], fn_vars := [],
    fn_temps := mainTemps kind,
    fn_body := .Ssequence (mainBody cap k args kind) (.Sreturn (some (.Econst_int 0 tint))) }

/-! ## Input -/

/-- The identifier of `lx_in`. -/
def inId : ident := 32

/-- `volatile unsigned char`, the type of the bytes of `lx_in`, which `clightgen` prints as
`tvolatile tuchar`. -/
def inByte : type := .Tint .I8 .Unsigned { attr_volatile := true, attr_alignas := none }

def inPtr : type := .Tpointer inByte noattr

/-- The type that `clightgen` gives `lx_in`, an array of no elements. -/
def inArray : type := .Tarray inByte 0 noattr

/-- `extern volatile const unsigned char lx_in[];`, which `clightgen` describes without
initialization data and without the qualifier `const`. -/
def inVar : globvar type :=
  { gvar_info := inArray, gvar_init := [], gvar_readonly := false, gvar_volatile := true }

/-- The definitions after the translation's in a program with input: `lx_in`, `lx_out`, and
`main`. -/
def inTail (main : function) : List (ident × globdef (fundef function) type) :=
  [(inId, .Gvar inVar), (outId, .Gvar outVar), (mainId, .Gfun (.Internal main))]

/-- The largest length that `main` accepts, `2 ^ 24 - 8`, so that its reads stay in the 16 MiB
that the linker script reserves from `lx_in`. -/
def inMax : Nat := 2 ^ 24 - 8

/-- The result of `main` for an input longer than `inMax`. -/
def inTooLong : Nat := 64

/-- The temporaries of `main` with input: the length `l3`, the array's address `l4`, the index
`l5`, the byte read `l6`, and the temporaries that `clightgen` creates for the load of the
length, the call of `alloc`, the load of a byte of the message, and the call of the entry. -/
def nTemp : ident := localId 3
def ptrTemp : ident := localId 4
def jTemp : ident := localId 5
def byteTemp : ident := localId 6
def lenLoadTemp : ident := callId 0
def allocTemp : ident := callId 1
def copyLoadTemp : ident := callId 2
def inCallTemp : ident := callId 3

/-- `x = lx_in[i];`, through the temporary `t`. -/
def inLoad (t x : ident) (i : expr) : statement :=
  .Ssequence
    (.Sbuiltin (some t) (.EF_vload .Mint8unsigned) [inPtr]
      [.Eaddrof (.Ederef (.Ebinop .Oadd (.Evar inId inArray) i inPtr) inByte) inPtr])
    (.Sset x (.Ecast (.Etempvar t inByte) tulong))

/-- `while (l5 < 8ULL) { l6 = lx_in[l5]; l3 = l3 | l6 << 8ULL * l5; l5 = l5 + 1ULL; }`. -/
def lenLoop : statement :=
  .Sloop
    (.Ssequence
      (.Sifthenelse (.Ebinop .Olt (.Etempvar jTemp tulong) (clong 8) tint) .Sskip .Sbreak)
      (.Ssequence (inLoad lenLoadTemp byteTemp (.Etempvar jTemp tulong))
        (.Ssequence
          (.Sset nTemp (.Ebinop .Oor (.Etempvar nTemp tulong)
            (.Ebinop .Oshl (.Etempvar byteTemp tulong)
              (.Ebinop .Omul (clong 8) (.Etempvar jTemp tulong) tulong) tulong) tulong))
          (.Sset jTemp (.Ebinop .Oadd (.Etempvar jTemp tulong) (clong 1) tulong)))))
    .Sskip

/-- `if (l3 > inMax) return (int) 64U;`. -/
def tooLongTest : statement :=
  .Sifthenelse (.Ebinop .Ogt (.Etempvar nTemp tulong) (clong inMax) tint)
    (.Sreturn (some (.Ecast (cint inTooLong) tint))) .Sskip

/-- `(l3 + 7ULL) >> 3ULL`, the number of words of the array. -/
def wordCount : expr :=
  .Ebinop .Oshr (.Ebinop .Oadd (.Etempvar nTemp tulong) (clong 7) tulong) (clong 3) tulong

/-- `l4 = lxf_0(8ULL + wordCount * 8ULL);`: the allocation of the array through `alloc`. -/
def allocCall : statement :=
  .Ssequence
    (.Scall (some allocTemp) (.Evar (funId 0) (.Tfunction [tulong] tulong cc_default))
      [.Ebinop .Oadd (clong 8) (.Ebinop .Omul wordCount (clong 8) tulong) tulong])
    (.Sset ptrTemp (.Etempvar allocTemp tulong))

/-- The stores of the array's length word, the number of words in `l6`, from the address in
`l4`. -/
def lengthWord (cap : Nat) : statement := storeBytes cap ptrTemp (.Etempvar byteTemp tulong) 0 7

/-- `while (l5 < l3) { l6 = lx_in[8ULL + l5];
((unsigned char *) lx_mem)[l4 + 8ULL + l5] = (unsigned char) l6; l5 = l5 + 1ULL; }`. -/
def copyLoop (cap : Nat) : statement :=
  .Sloop
    (.Ssequence
      (.Sifthenelse (.Ebinop .Olt (.Etempvar jTemp tulong) (.Etempvar nTemp tulong) tint)
        .Sskip .Sbreak)
      (.Ssequence
        (inLoad copyLoadTemp byteTemp (.Ebinop .Oadd (clong 8) (.Etempvar jTemp tulong) tulong))
        (.Ssequence
          (.Sassign
            (byteAt cap (.Ebinop .Oadd (.Ebinop .Oadd (.Etempvar ptrTemp tulong) (clong 8) tulong)
              (.Etempvar jTemp tulong) tulong))
            (.Ecast (.Etempvar byteTemp tulong) tuchar))
          (.Sset jTemp (.Ebinop .Oadd (.Etempvar jTemp tulong) (clong 1) tulong)))))
    .Sskip

/-- The call of the entry `k` on the array's address and the length. -/
def inEntry (kind : OutKind) (k : Nat) : statement :=
  let args := [.Etempvar ptrTemp tulong, .Etempvar nTemp tulong]
  match kind with
  | .words _ => voidCall k [tulong, tulong] args
  | _ => resultCall inCallTemp k [tulong, tulong] args

/-- The body of `main` with input before the `return 0;` that `clightgen` appends. -/
def inBody (cap k : Nat) (kind : OutKind) : statement :=
  seqList ([initCall, .Sset nTemp (clong 0), .Sset jTemp (clong 0), lenLoop, tooLongTest,
    allocCall, statusTest, .Sset byteTemp wordCount, lengthWord cap, .Sset jTemp (clong 0),
    copyLoop cap, inEntry kind k, statusTest] ++ outStmts cap kind)

/-- The temporaries that `main` declares for the result. -/
def outTemps : OutKind → List (ident × type)
  | .word => [(resTemp, tulong)]
  | .array => [(resTemp, tulong), (lenTemp, tulong), (idxTemp, tulong)]
  | .words _ => []

def inTemps (kind : OutKind) : List (ident × type) :=
  outTemps kind ++ [(nTemp, tulong), (ptrTemp, tulong), (jTemp, tulong), (byteTemp, tulong)] ++
    (match kind with
      | .words _ => []
      | _ => [(inCallTemp, tulong)]) ++
    [(copyLoadTemp, inByte), (allocTemp, tulong), (lenLoadTemp, inByte)]

/-- `main` with input, which calls the entry `k` on the array of the input and its length and
writes its result of the kind `kind`. -/
def inMain (cap k : Nat) (kind : OutKind) : function :=
  { fn_return := tint, fn_callconv := cc_default, fn_params := [], fn_vars := [],
    fn_temps := inTemps kind,
    fn_body := .Ssequence (inBody cap k kind) (.Sreturn (some (.Econst_int 0 tint))) }

section

variable (gname : ident → String) (tname : ident → String) (isCall : ident → Bool)

def cdecls (temps : List (ident × type)) : Except String String := do
  let decls ← (temps.filter fun (t, _) => !isCall t).mapM fun (t, ty) => do
    pure s!"  {← ctype ty} {tname t};\n"
  pure (String.join decls)

/-- The C text of `lx_out`'s declaration and of `main`, without the `return 0;` that `clightgen`
appends, to follow the C text of the translation. -/
def cmain (cap k : Nat) (args : List UInt64) (kind : OutKind) : Except String String := do
  pure ("extern volatile unsigned int lx_out;\n" ++ "int main(void) {\n" ++
    (← cdecls tname isCall (mainTemps kind)) ++
    (← cstmt gname tname isCall 1 (mainBody cap k args kind)) ++ "}\n")

/-- The C text of the declarations of `lx_in` and `lx_out` and of `main` with input. -/
def cinMain (cap k : Nat) (kind : OutKind) : Except String String := do
  pure ("extern volatile const unsigned char lx_in[];\n" ++
    "extern volatile unsigned int lx_out;\n" ++ "int main(void) {\n" ++
    (← cdecls tname isCall (inTemps kind)) ++
    (← cstmt gname tname isCall 1 (inBody cap k kind)) ++ "}\n")

end

/-- The bytes of a word, from the lowest. -/
def encodeWord (x : UInt64) : List UInt8 :=
  (List.range 8).map fun j => (x >>> UInt64.ofNat (8 * j)).toUInt8

/-- The bytes of an array of words in memory: its length word, then its elements. -/
def encodeArray (xs : Array UInt64) : List UInt8 :=
  encodeWord (UInt64.ofNat xs.size) ++ xs.toList.flatMap encodeWord

/-- The bytes of words in the result globals, each from the lowest. -/
def encodeWords (ws : List UInt64) : List UInt8 := ws.flatMap encodeWord

/-- The trace of `main`'s output: one store of `unsigned int` to `lx_out` per byte. -/
def outTrace (bs : List UInt8) : trace :=
  bs.map fun b => .Event_vstore .Mint32 outId Ptrofs.zero (.EVint (UInt32.ofNat b.toNat))

/-- The C text of the bare-metal program of the translation `t`: the translation's text, then
`lx_out` and `main`. -/
def Translation.bareText (t : Translation) (cap k : Nat) (args : List UInt64) (kind : OutKind) :
    Except String String := do
  let gname (id : ident) : String := if id == outId then "lx_out" else t.gname id
  pure ((← t.text) ++ (← cmain gname tempName isCallTemp cap k args kind))

/-- The C text of the program with input of the translation `t`: the translation's text, then
`lx_in`, `lx_out`, and `main`. -/
def Translation.inText (t : Translation) (cap k : Nat) (kind : OutKind) : Except String String := do
  let gname (id : ident) : String :=
    if id == outId then "lx_out" else if id == inId then "lx_in" else t.gname id
  pure ((← t.text) ++ (← cinMain gname tempName isCallTemp cap k kind))

end LeanExe.Native
