import LeanExe.Native.Clight.Run
import LeanExe.Native.Print

/-!
Random Clight programs for the differential test of `LClight.run` against CompCert's reference
interpreter.  A program has six globals (`g_u32`, `g_u64`, `g_f64`, `g_f32`, the array `arr` of
eight words, and `pun`), a function `helper (x, y)`, and a function `test ()` that returns an
`unsigned long long`.  The statements assign temporaries, globals, array elements, and `pun`
read as a `double`; they branch, loop a bounded number of times, call `helper`, and call
`__builtin_fsqrt`.  The expressions combine constants biased toward edge values, temporaries,
and globals with the operators and casts of `Cop.lean`, `Oabsfloat` among them, at the types
`unsigned int`, `int`, `unsigned long long`, `double`, and `float`.  Some operations can be undefined, such as a shift
by the word size or more, a division by zero, and a conversion of a float out of range; most are
guarded so that they are defined.  `pun` starts as a NaN or an infinity half of the time, the
only way a NaN with a chosen payload can enter a program.

`cText` is the program in C with a `main` that calls `test` and prints the result and the
globals' bits, and `expected` is what `LClight.run` gives for the same lines, or `UB`.

A trace program, from `genTraceProgram`, has five more globals, volatile ones of the types
`unsigned char`, `signed char`, `unsigned short`, `unsigned int`, and `unsigned long long`
(`g_v8`, `g_vs8`, `g_v16`, `g_v32`, and `g_v64`), and its function `main ()`, of the type
`int(void)`, has the statements of `test` and stores of integers to the volatile globals, in the
form `Sbuiltin None (EF_vstore chunk)` that SimplExpr gives an assignment to a volatile lvalue.
`traceText` is the program in C, and `expectedTrace` is what `LClight.run_program` gives: one
line per volatile store and the exit code, as CompCert's reference interpreter prints them, or
`UB`.
-/

namespace TestSupport.Native.ClightGen

open LClight

instance : Inhabited statement := ⟨.Sskip⟩
instance : Inhabited binary_operation := ⟨.Oadd⟩
instance : Inhabited unary_operation := ⟨.Oneg⟩
instance : Inhabited type := ⟨.Tvoid⟩
instance : Inhabited memory_chunk := ⟨.Mint32⟩

abbrev Gen := StateM StdGen

def rand (n : Nat) : Gen Nat := do
  let g ← get
  let (x, g') := randNat g 0 (n - 1)
  set g'
  pure x

def pick [Inhabited α] (l : List α) : Gen α := do
  let i ← rand l.length
  pure (l.getD i default)

/-- An edge value with probability one half, and otherwise a uniform value below `bound`. -/
def edgeOr (edges : List Nat) (bound : Nat) : Gen Nat := do
  if (← rand 2) == 0 then pick edges else rand bound

def tuint : type := .Tint .I32 .Unsigned noattr
def tint : type := .Tint .I32 .Signed noattr
def tulong : type := .Tlong .Unsigned noattr
def tdouble : type := .Tfloat .F64 noattr
def tfloat : type := .Tfloat .F32 noattr
def tarr : type := .Tarray tulong 8 noattr

inductive Ty where
  | u32 | i32 | u64 | f64 | f32
  deriving Repr, DecidableEq, Inhabited

def Ty.type : Ty → type
  | .u32 => tuint
  | .i32 => tint
  | .u64 => tulong
  | .f64 => tdouble
  | .f32 => tfloat

def allTys : List Ty := [.u32, .i32, .u64, .f64, .f32]

/-! ## Identifiers -/

def idU32 : ident := 1
def idU64 : ident := 2
def idF64 : ident := 3
def idF32 : ident := 4
def idArr : ident := 5
def idPun : ident := 6
def idHelper : ident := 7
def idTest : ident := 8
def idX : ident := 20
def idY : ident := 21
def idHr : ident := 22
def idMain : ident := 9

/-- The volatile globals of a trace program: identifier, type, and memory chunk. -/
def volatileAttr : attr := { attr_volatile := true, attr_alignas := none }
def volatileGlobals : List (ident × type × memory_chunk) := [
  (10, .Tint .I8 .Unsigned volatileAttr, .Mint8unsigned),
  (11, .Tint .I8 .Signed volatileAttr, .Mint8signed),
  (12, .Tint .I16 .Unsigned volatileAttr, .Mint16unsigned),
  (13, .Tint .I32 .Unsigned volatileAttr, .Mint32),
  (14, .Tlong .Unsigned volatileAttr, .Mint64)]

/-- The temporaries of `test`, three of each type but `int`, which has one, and then the loop
counters. -/
def testTemps (t : Ty) : List ident :=
  match t with
  | .u32 => [30, 31, 32]
  | .u64 => [33, 34, 35]
  | .f64 => [36, 37, 38]
  | .f32 => [39, 40, 41]
  | .i32 => [42]

def counters : List ident := [43, 44, 45]

def name (id : ident) : String :=
  match id with
  | 1 => "g_u32" | 2 => "g_u64" | 3 => "g_f64" | 4 => "g_f32" | 5 => "arr" | 6 => "pun"
  | 7 => "helper" | 8 => "test" | 9 => "main" | 10 => "g_v8" | 11 => "g_vs8" | 12 => "g_v16"
  | 13 => "g_v32" | 14 => "g_v64" | 20 => "x" | 21 => "y" | 22 => "hr"
  | n => s!"t{n}"

/-! ## Constants -/

def finiteDouble : Gen Nat := do
  let edges := [0, 0x8000000000000000, 0x3FF0000000000000, 0xBFF0000000000000,
    0x3FE0000000000000, 0x43E0000000000000, 0x43F0000000000000, 0xC3E0000000000000,
    0x41DFFFFFFFC00000, 0x41E0000000000000, 0x7FEFFFFFFFFFFFFF, 1, 0x000FFFFFFFFFFFFF,
    0x43EFFFFFFFFFFFFF, 0x3CA0000000000000]
  match (← rand 3) with
  | 0 => pick edges
  | 1 => do
      -- A magnitude between 2^-10 and 2^32, which a conversion to an integer type often keeps
      -- in range.
      let sign := (← rand 2) * 2 ^ 63
      let exponent := 1023 - 10 + (← rand 43)
      pure (sign + exponent * 2 ^ 52 + (← rand (2 ^ 52)))
  | _ => do
      let b ← rand (2 ^ 64)
      -- An exponent of all ones is a NaN or an infinity, which has no literal.
      pure (if b / 2 ^ 52 % 2 ^ 11 == 0x7FF then b - 2 ^ 52 else b)

def finiteFloat : Gen Nat := do
  let edges := [0, 0x80000000, 0x3F800000, 0xBF800000, 0x3F000000, 0x5F000000, 0x5F800000,
    0x4F000000, 0xCF000000, 0x7F7FFFFF, 1, 0x007FFFFF, 0x5F7FFFFF]
  match (← rand 3) with
  | 0 => pick edges
  | 1 => do
      let sign := (← rand 2) * 2 ^ 31
      let exponent := 127 - 10 + (← rand 43)
      pure (sign + exponent * 2 ^ 23 + (← rand (2 ^ 23)))
  | _ => do
      let b ← rand (2 ^ 32)
      pure (if b / 2 ^ 23 % 2 ^ 8 == 0xFF then b - 2 ^ 23 else b)

/-- The initial bits of `pun`: a NaN or an infinity half of the time, with either sign and,
for a NaN, a quiet or signaling payload, so that the NaN rules of the two targets come into
play; otherwise uniform. -/
def punBits : Gen Nat := do
  if (← rand 2) == 0 then
    let sign := (← rand 2) * 2 ^ 63
    let payload ← if (← rand 2) == 0 then pick [0, 1, 2 ^ 51, 2 ^ 51 + 1, 2 ^ 52 - 1]
      else rand (2 ^ 52)
    pure (sign + 0x7FF * 2 ^ 52 + payload)
  else rand (2 ^ 64)

def constOf : Ty → Gen expr
  | .u32 => do
      let n ← edgeOr [0, 1, 2, 7, 31, 32, 33, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF] (2 ^ 32)
      pure (.Econst_int (UInt32.ofNat n) tuint)
  | .i32 => do
      let n ← edgeOr [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 0xFFFFFFFE] (2 ^ 32)
      pure (.Econst_int (UInt32.ofNat n) tint)
  | .u64 => do
      let n ← edgeOr [0, 1, 7, 63, 64, 65, 2 ^ 32, 2 ^ 32 - 1, 2 ^ 63, 2 ^ 63 - 1, 2 ^ 64 - 1]
        (2 ^ 64)
      pure (.Econst_long (UInt64.ofNat n) tulong)
  | .f64 => do pure (.Econst_float (UInt64.ofNat (← finiteDouble)) tdouble)
  | .f32 => do pure (.Econst_single (UInt32.ofNat (← finiteFloat)) tfloat)

/-! ## Expressions -/

/-- `pun` read or written as a `double`. -/
def punDouble : expr :=
  .Ederef (.Ecast (.Eaddrof (.Evar idPun tulong) (.Tpointer tulong noattr))
    (.Tpointer tdouble noattr)) tdouble

def arrElem (index : expr) : expr :=
  .Ederef (.Ebinop .Oadd (.Evar idArr tarr) index (.Tpointer tulong noattr)) tulong

def globalOf : Ty → Gen expr
  | .u32 => pure (.Evar idU32 tuint)
  | .u64 => do pick [expr.Evar idU64 tulong, .Evar idPun tulong]
  | .f64 => do pick [expr.Evar idF64 tdouble, punDouble]
  | .f32 => pure (.Evar idF32 tfloat)
  | .i32 => constOf .i32

structure Ctx where
  temps : Ty → List ident
  /-- Whether statements may store to the volatile globals of a trace program. -/
  volatiles : Bool := false

def leaf (c : Ctx) (t : Ty) : Gen expr := do
  let k ← rand 4
  if k == 0 then constOf t
  else if k == 1 then globalOf t
  else
    match c.temps t with
    | [] => constOf t
    | temps => do pure (.Etempvar (← pick temps) t.type)

def intOps : List binary_operation := [.Oadd, .Osub, .Omul, .Oand, .Oor, .Oxor]
def floatOps : List binary_operation := [.Oadd, .Osub, .Omul, .Odiv]
def cmpOps : List binary_operation := [.Oeq, .One, .Olt, .Ogt, .Ole, .Oge]

/-- Usually `b | 1`, which is not zero. -/
def divisor (b : expr) (one : expr) (ty : type) : Gen expr := do
  if (← rand 16) == 0 then pure b else pure (.Ebinop .Oor b one ty)

/-- Usually `b & mask`, which is below the word size. -/
def amount (b : expr) (mask : expr) (ty : type) : Gen expr := do
  if (← rand 16) == 0 then pure b else pure (.Ebinop .Oand b mask ty)

def genExpr (c : Ctx) : Nat → Ty → Gen expr
  | 0, t => leaf c t
  | d + 1, t => do
    if (← rand 10) < 3 then leaf c t
    else
      match t with
      | .u32 =>
          match (← rand 8) with
          | 0 => do
              let op ← pick intOps
              pure (.Ebinop op (← genExpr c d .u32) (← genExpr c d .u32) tuint)
          | 1 => do
              let op ← pick [binary_operation.Odiv, .Omod]
              let b ← divisor (← genExpr c d .u32) (.Econst_int 1 tuint) tuint
              pure (.Ebinop op (← genExpr c d .u32) b tuint)
          | 2 => do
              let op ← pick [binary_operation.Oshl, .Oshr]
              let b ← amount (← genExpr c d .u32) (.Econst_int 31 tuint) tuint
              pure (.Ebinop op (← genExpr c d .u32) b tuint)
          | 3 => do
              let s ← pick allTys
              let op ← pick cmpOps
              pure (.Ecast (.Ebinop op (← genExpr c d s) (← genExpr c d s) tint) tuint)
          | 4 => do pure (.Ecast (← genExpr c d .u64) tuint)
          | 5 => do pure (.Ecast (← genExpr c d .i32) tuint)
          | 6 => do
              let op ← pick [unary_operation.Onotint, .Oneg]
              pure (.Eunop op (← genExpr c d .u32) tuint)
          | _ => do
              let b ← amount (← genExpr c d .u64) (.Econst_long 31 tulong) tulong
              pure (.Ebinop .Oshl (← genExpr c d .u32) b tuint)
      | .i32 =>
          match (← rand 7) with
          | 0 => do
              let s ← pick allTys
              let op ← pick cmpOps
              pure (.Ebinop op (← genExpr c d s) (← genExpr c d s) tint)
          | 1 => do
              let op ← pick (intOps ++ [.Oshr])
              pure (.Ebinop op (← genExpr c d .i32) (← genExpr c d .i32) tint)
          | 2 => do
              let op ← pick [binary_operation.Odiv, .Omod]
              let b ← divisor (← genExpr c d .i32) (.Econst_int 1 tint) tint
              pure (.Ebinop op (← genExpr c d .i32) b tint)
          | 3 => do pure (.Ecast (← genExpr c d .u32) tint)
          | 4 => do
              let s ← pick allTys
              pure (.Eunop .Onotbool (← genExpr c d s) tint)
          | 5 => do
              let op ← pick [unary_operation.Onotint, .Oneg]
              pure (.Eunop op (← genExpr c d .i32) tint)
          | _ => do pure (.Ecast (← genExpr c d .f32) tint)
      | .u64 =>
          match (← rand 10) with
          | 0 => do
              let op ← pick intOps
              pure (.Ebinop op (← genExpr c d .u64) (← genExpr c d .u64) tulong)
          | 1 => do
              let op ← pick [binary_operation.Odiv, .Omod]
              let b ← divisor (← genExpr c d .u64) (.Econst_long 1 tulong) tulong
              pure (.Ebinop op (← genExpr c d .u64) b tulong)
          | 2 => do
              let op ← pick [binary_operation.Oshl, .Oshr]
              let b ← amount (← genExpr c d .u64) (.Econst_long 63 tulong) tulong
              pure (.Ebinop op (← genExpr c d .u64) b tulong)
          | 3 => do
              let index : expr := .Ebinop .Oand (← genExpr c d .u64) (.Econst_long 7 tulong) tulong
              pure (arrElem index)
          | 4 => do pure (.Ecast (← genExpr c d .u32) tulong)
          | 5 => do pure (.Ecast (← genExpr c d .i32) tulong)
          | 6 => do pure (.Ecast (← genExpr c d .f64) tulong)
          | 7 => do pure (.Ecast (← genExpr c d .f32) tulong)
          | 8 => do
              let op ← pick [unary_operation.Onotint, .Oneg]
              pure (.Eunop op (← genExpr c d .u64) tulong)
          | _ => do
              let op ← pick intOps
              pure (.Ebinop op (← genExpr c d .u32) (← genExpr c d .u64) tulong)
      | .f64 =>
          match (← rand 7) with
          | 0 => do
              let op ← pick floatOps
              pure (.Ebinop op (← genExpr c d .f64) (← genExpr c d .f64) tdouble)
          | 1 => do pure (.Ecast (← genExpr c d .u64) tdouble)
          | 2 => do pure (.Ecast (← genExpr c d .f32) tdouble)
          | 3 => do pure (.Ecast (← genExpr c d .i32) tdouble)
          | 4 => do pure (.Ecast (← genExpr c d .u32) tdouble)
          | 5 => do
              let op ← pick [unary_operation.Oneg, .Oabsfloat]
              pure (.Eunop op (← genExpr c d .f64) tdouble)
          | _ => do
              let op ← pick floatOps
              pure (.Ebinop op (← genExpr c d .f32) (← genExpr c d .f64) tdouble)
      | .f32 =>
          match (← rand 6) with
          | 0 => do
              let op ← pick floatOps
              pure (.Ebinop op (← genExpr c d .f32) (← genExpr c d .f32) tfloat)
          | 1 => do pure (.Ecast (← genExpr c d .f64) tfloat)
          | 2 => do pure (.Ecast (← genExpr c d .u64) tfloat)
          | 3 => do pure (.Ecast (← genExpr c d .i32) tfloat)
          | 4 => do pure (.Eunop .Oneg (← genExpr c d .f32) tfloat)
          | _ => do pure (.Ecast (← genExpr c d .u32) tfloat)

/-! ## Statements -/

def seqs : List statement → statement
  | [] => .Sskip
  | [s] => s
  | s :: rest => .Ssequence s (seqs rest)

def sqrtSig : signature := { sig_args := [.Xfloat], sig_res := .Xfloat, sig_cc := cc_default }

def helperType : type := .Tfunction [tulong, tdouble] tulong cc_default

/-- A statement of `test` at nesting `depth`, inside `loops` loops, with the loop counters
`free` still unused. -/
def genStmt (c : Ctx) : Nat → Nat → List ident → Gen statement
  | 0, _, _ => do
      let t ← pick [Ty.u32, .u64, .f64, .f32, .i32]
      pure (.Sset (← pick (testTemps t)) (← genExpr c 3 t))
  | depth + 1, loops, free => do
      match (← rand (if c.volatiles then 14 else 12)) with
      | 0 | 1 => do
          let t ← pick allTys
          pure (.Sset (← pick (testTemps t)) (← genExpr c 3 t))
      | 2 => do
          let t ← pick [Ty.u32, .u64, .f64, .f32]
          let lhs ← globalOf t
          pure (.Sassign lhs (← genExpr c 3 t))
      | 3 => do
          let index : expr := .Ebinop .Oand (← genExpr c 2 .u64) (.Econst_long 7 tulong) tulong
          pure (.Sassign (arrElem index) (← genExpr c 3 .u64))
      | 4 => do pure (.Sassign punDouble (← genExpr c 3 .f64))
      | 5 | 6 => do
          let t ← pick allTys
          let s1 ← genStmt c depth loops free
          let s2 ← genStmt c depth loops free
          pure (.Sifthenelse (← genExpr c 2 t) s1 s2)
      | 7 =>
          match free with
          | [] => genStmt c depth loops free
          | ctr :: rest => do
              let bound ← rand 5
              let body ← genStmt c depth (loops + 1) rest
              let ctrE : expr := .Etempvar ctr tulong
              pure (.Ssequence (.Sset ctr (.Econst_long 0 tulong))
                (.Sloop
                  (.Ssequence
                    (.Sifthenelse (.Ebinop .Oge ctrE (.Econst_long (UInt64.ofNat bound) tulong) tint)
                      .Sbreak .Sskip)
                    (.Ssequence (.Sset ctr (.Ebinop .Oadd ctrE (.Econst_long 1 tulong) tulong))
                      body))
                  .Sskip))
      | 8 => do
          let r ← pick (testTemps .u64)
          pure (.Scall (some r) (.Evar idHelper helperType)
            [← genExpr c 2 .u64, ← genExpr c 2 .f64])
      | 9 => do
          let r ← pick (testTemps .f64)
          pure (.Sbuiltin (some r) (.EF_builtin "__builtin_fsqrt" sqrtSig) [tdouble]
            [← genExpr c 2 .f64])
      | 10 =>
          if loops == 0 then genStmt c depth loops free
          else pick [statement.Sbreak, .Scontinue]
      | 12 | 13 => do
          let (id, ty, chunk) ← pick volatileGlobals
          let ptr : type := .Tpointer ty noattr
          let e ← genExpr c 3 (← pick [Ty.u32, .i32, .u64])
          pure (.Sbuiltin none (.EF_vstore chunk) [ptr, ty] [.Eaddrof (.Evar id ty) ptr, e])
      | _ => do
          let s1 ← genStmt c depth loops free
          let s2 ← genStmt c depth loops free
          pure (.Ssequence s1 s2)

def allTestTemps : List (ident × type) :=
  (allTys.flatMap fun t => (testTemps t).map fun id => (id, t.type)) ++
    counters.map fun id => (id, tulong)

/-- The function `test`, or with `vol` the function `main` of a trace program, which stores to
the volatile globals and returns an `int`. -/
def genTest (vol : Bool := false) : Gen function := do
  let c : Ctx := { temps := testTemps, volatiles := vol }
  let temps := allTys.flatMap fun t => (testTemps t).map fun id => (id, t)
  let inits ← temps.mapM fun (id, t) => do pure (statement.Sset id (← constOf t))
  let n ← rand 6
  let body ← (List.range (n + 1)).mapM fun _ => genStmt c 3 0 counters
  -- A final store of a computed `double` and `float`, so that the printed globals more often
  -- show a NaN that the program computed.
  let lhs ← globalOf .f64
  let finalStores := [statement.Sassign lhs (← genExpr c 3 .f64),
    .Sassign (.Evar idF32 tfloat) (← genExpr c 3 .f32)]
  let result ← genExpr c 3 .u64
  pure { fn_return := if vol then tint else tulong, fn_callconv := cc_default, fn_params := [],
         fn_vars := [], fn_temps := allTestTemps,
         fn_body := seqs (inits ++ body ++ finalStores ++ [.Sreturn (some result)]) }

def genHelper : Gen function := do
  let c : Ctx := { temps := fun t => match t with
    | .u64 => [idX]
    | .f64 => [idY]
    | _ => [] }
  let e ← genExpr c 3 .u64
  let g ← genExpr c 2 .u64
  pure { fn_return := tulong, fn_callconv := cc_default,
         fn_params := [(idX, tulong), (idY, tdouble)], fn_vars := [],
         fn_temps := [(idHr, tulong)],
         fn_body := seqs [.Sset idHr e, .Sassign (.Evar idU64 tulong) g,
           .Sreturn (some (.Etempvar idHr tulong))] }

def gvar (ty : type) (init : List init_data) : globdef (fundef function) type :=
  .Gvar { gvar_info := ty, gvar_init := init, gvar_readonly := false, gvar_volatile := false }

def programOf (u32 : UInt32) (u64 f64 : UInt64) (f32 : UInt32) (arr : List init_data)
    (pun : UInt64) (helper test : function) : program function :=
  { prog_defs := [
      (idU32, gvar tuint [.Init_int32 u32]),
      (idU64, gvar tulong [.Init_int64 u64]),
      (idF64, gvar tdouble [.Init_float64 f64]),
      (idF32, gvar tfloat [.Init_float32 f32]),
      (idArr, gvar tarr arr),
      (idPun, gvar tulong [.Init_int64 pun]),
      (idHelper, .Gfun (.Internal helper)),
      (idTest, .Gfun (.Internal test))],
    prog_public := [], prog_main := idTest }

def genProgram : Gen (program function) := do
  let u32 := UInt32.ofNat (← rand (2 ^ 32))
  let u64 := UInt64.ofNat (← rand (2 ^ 64))
  let f64 := UInt64.ofNat (← finiteDouble)
  let f32 := UInt32.ofNat (← finiteFloat)
  let arr ← (List.range 8).mapM fun _ => do pure (init_data.Init_int64 (UInt64.ofNat (← rand (2 ^ 64))))
  let pun := UInt64.ofNat (← punBits)
  let helper ← genHelper
  let test ← genTest
  pure (programOf u32 u64 f64 f32 arr pun helper test)

/-- A volatile global of the type `ty` with `size` zero bytes. -/
def volatileVar (ty : type) (size : Nat) : globdef (fundef function) type :=
  .Gvar { gvar_info := ty, gvar_init := [.Init_space size], gvar_readonly := false,
          gvar_volatile := true }

def chunkSize : memory_chunk → Nat
  | .Mint8signed | .Mint8unsigned | .Mbool => 1
  | .Mint16signed | .Mint16unsigned => 2
  | .Mint32 | .Mfloat32 | .Many32 => 4
  | .Mint64 | .Mfloat64 | .Many64 => 8

/-- A trace program: the globals of `programOf`, the volatile globals, `helper`, and `main`. -/
def genTraceProgram : Gen (program function) := do
  let u32 := UInt32.ofNat (← rand (2 ^ 32))
  let u64 := UInt64.ofNat (← rand (2 ^ 64))
  let f64 := UInt64.ofNat (← finiteDouble)
  let f32 := UInt32.ofNat (← finiteFloat)
  let arr ← (List.range 8).mapM fun _ => do pure (init_data.Init_int64 (UInt64.ofNat (← rand (2 ^ 64))))
  let pun := UInt64.ofNat (← punBits)
  let helper ← genHelper
  let main ← genTest true
  let base := programOf u32 u64 f64 f32 arr pun helper main
  let vars := volatileGlobals.map fun (id, ty, chunk) => (id, volatileVar ty (chunkSize chunk))
  pure { prog_defs := base.prog_defs.take 6 ++ vars ++
           [(idHelper, .Gfun (.Internal helper)), (idMain, .Gfun (.Internal main))],
         prog_public := [], prog_main := idMain }

/-! ## Programs for the NaN parameters -/

def dzero : expr := .Econst_float 0 tdouble
def dOne : expr := .Econst_float 0x3FF0000000000000 tdouble
def fzero : expr := .Econst_single 0 tfloat
def dnan : expr := .Ebinop .Odiv dzero dzero tdouble
def fnan : expr := .Ebinop .Odiv fzero fzero tfloat
def setF64 (e : expr) : statement := .Sassign (.Evar idF64 tdouble) e
def setF32 (e : expr) : statement := .Sassign (.Evar idF32 tfloat) e

/-- Statements whose results depend on the NaN parameters of `Archi`, each with the initial bits
of `pun`: the default NaNs of both formats, a quiet and a signaling operand in both orders, two
quiet operands, the square root of a negative number, conversions of NaNs between the formats,
and negation of a NaN; then `__builtin_fabs` of zeros, infinities, and NaNs, whose results the
parameters do not change. -/
def nanCases : List (UInt64 × statement) := [
  (0, setF64 dnan),
  (0, setF32 fnan),
  (0x7FF0000000000001, setF64 (.Ebinop .Oadd dnan punDouble tdouble)),
  (0x7FF0000000000001, setF64 (.Ebinop .Oadd punDouble dnan tdouble)),
  (0xFFF8000000000005, setF64 (.Ebinop .Omul dnan punDouble tdouble)),
  (0, .Ssequence
    (.Sbuiltin (some 36) (.EF_builtin "__builtin_fsqrt" sqrtSig) [tdouble]
      [.Eunop .Oneg dOne tdouble])
    (setF64 (.Etempvar 36 tdouble))),
  (0, setF32 (.Ecast dnan tfloat)),
  (0, setF64 (.Ecast fnan tdouble)),
  (0x7FF4000000000000, setF32 (.Ecast punDouble tfloat)),
  (0x7FF8000000000003, setF64 (.Eunop .Oneg punDouble tdouble)),
  (0x7FFC000000000000, setF32 (.Ebinop .Oadd fnan (.Ecast punDouble tfloat) tfloat))] ++
  -- `__builtin_fabs` of both zeros, both infinities, a positive and a negative quiet NaN with
  -- payloads, and a signaling NaN.
  ([0, 0x8000000000000000, 0x7FF0000000000000, 0xFFF0000000000000, 0x7FF8000000000005,
    0xFFF8000000000007, 0x7FF0000000000003].map fun bits =>
    (bits, setF64 (.Eunop .Oabsfloat punDouble tdouble)))

def nanPrograms : List (program function) :=
  let helper : function :=
    { fn_return := tulong, fn_callconv := cc_default,
      fn_params := [(idX, tulong), (idY, tdouble)], fn_vars := [], fn_temps := [],
      fn_body := .Sreturn (some (.Etempvar idX tulong)) }
  nanCases.map fun (pun, s) =>
    programOf 0 0 0 0 (List.replicate 8 (.Init_int64 0)) pun helper
      { fn_return := tulong, fn_callconv := cc_default, fn_params := [], fn_vars := [],
        fn_temps := allTestTemps,
        fn_body := .Ssequence s (.Sreturn (some (.Econst_long 0 tulong))) }

/-! ## C text and expected output -/

def cMain : String :=
  "int printf(const char *, ...);\n" ++
  "int main(void) {\n" ++
  "  unsigned long long r = test();\n" ++
  "  printf(\"r %llx\\n\", r);\n" ++
  "  printf(\"g_u32 %x\\n\", g_u32);\n" ++
  "  printf(\"g_u64 %llx\\n\", g_u64);\n" ++
  "  printf(\"g_f64 %llx\\n\", *(unsigned long long *)&g_f64);\n" ++
  "  printf(\"g_f32 %x\\n\", *(unsigned int *)&g_f32);\n" ++
  "  for (int i = 0; i < 8; i++) printf(\"arr %llx\\n\", arr[i]);\n" ++
  "  printf(\"pun %llx\\n\", pun);\n" ++
  "  return 0;\n" ++
  "}\n"

def cText (p : program function) : Except String String := do
  pure ((← LeanExe.Native.cprogram name name (fun _ => false) p) ++ cMain)

def hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

/-- The bits of the `chunk`-sized value at offset `ofs` of the global `id` in `m`. -/
def bitsAt (p : program function) (m : mem) (id : ident) (chunk : memory_chunk) (ofs : Int) :
    Option Nat :=
  match Genv.find_symbol (globalenv p) id with
  | none => none
  | some b =>
      match Mem.load chunk m b ofs with
      | some (.Vint n) => some n.toNat
      | some (.Vlong n) => some n.toNat
      | _ => none

/-- The lines that `main` prints, or `UB`, or `FUEL` when the fuel ran out. -/
def expected (A : Archi) (p : program function) (fuel : Nat) : String :=
  match run A p idTest [] fuel with
  | .error .stuck => "UB\n"
  | .error .outOfFuel => "FUEL\n"
  | .ok (_, m, v) =>
      let line (label : String) (o : Option Nat) : String :=
        match o with
        | some n => s!"{label} {hex n}\n"
        | none => s!"{label} ?\n"
      let r := match v with
        | .Vlong n => some n.toNat
        | _ => none
      line "r" r ++
      line "g_u32" (bitsAt p m idU32 .Mint32 0) ++
      line "g_u64" (bitsAt p m idU64 .Mint64 0) ++
      line "g_f64" (bitsAt p m idF64 .Mint64 0) ++
      line "g_f32" (bitsAt p m idF32 .Mint32 0) ++
      String.join ((List.range 8).map fun (i : Nat) => line "arr" (bitsAt p m idArr .Mint64 (8 * (i : Int)))) ++
      line "pun" (bitsAt p m idPun .Mint64 0)

/-! ## Trace programs: C text and expected output -/

def traceText (p : program function) : Except String String :=
  LeanExe.Native.cprogram name name (fun _ => false) p

/-- `PrintAST.name_of_chunk` of CompCert's `common/PrintAST.ml`. -/
def chunkName : memory_chunk → String
  | .Mbool => "bool" | .Mint8signed => "int8s" | .Mint8unsigned => "int8u"
  | .Mint16signed => "int16s" | .Mint16unsigned => "int16u" | .Mint32 => "int32"
  | .Mint64 => "int64" | .Mfloat32 => "float32" | .Mfloat64 => "float64" | .Many32 => "any32"
  | .Many64 => "any64"

def signed32 (n : int) : Int := if n.toNat < 2 ^ 31 then n.toNat else (n.toNat : Int) - 2 ^ 32

def signed64 (n : int64) : Int :=
  if n.toNat < 2 ^ 63 then n.toNat else (n.toNat : Int) - 2 ^ 64

/-- An event as `ccomp -interp` prints it after `Time N: `, `print_event` of
`driver/Interp.ml`, for the integer event values that trace programs produce. -/
def eventLine : event → String
  | .Event_vstore chunk id ofs ev =>
      let o := signed64 ofs
      let ofsText := if o < 0 then s!"{o}" else s!"+{o}"
      let v := match ev with
        | .EVint n => s!"{signed32 n}"
        | .EVlong n => s!"{signed64 n}LL"
        | _ => "?"
      s!"observable event: volatile store {chunkName chunk}[&{name id}{ofsText}] <- {v}"
  | _ => "observable event: ?"

/-- The lines that `ccomp -interp` prints for a trace program, without the prefix `Time N: `,
or `UB`, or `FUEL` when the fuel ran out. -/
def expectedTrace (A : Archi) (p : program function) (fuel : Nat) : String :=
  match run_program A p fuel with
  | .error .stuck => "UB\n"
  | .error .outOfFuel => "FUEL\n"
  | .ok (t, r) =>
      String.join (t.map fun ev => eventLine ev ++ "\n") ++
        s!"program terminated (exit code = {signed32 r})\n"

end TestSupport.Native.ClightGen
