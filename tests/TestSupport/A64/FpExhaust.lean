import TestSupport.A64.FpVectors

/-!
The exhaustive test of the single-precision forms: each case runs the code that the generator
emits for one f32 operation on every 32-bit word, or on a range of chunks of them, in an arm64
Image that Lean writes, and compares a digest of each chunk's results with the digest of the
results of Talos's function of the operation.  A unary operation takes the word as its operand,
and a binary one takes it as one operand and a fixed word as the other.

A chunk holds `2^16` consecutive words, and its digest is `h`, from 0, updated by
`h := h * digestMul + lo` and then `h := h * digestMul + hi` for the low and high 32 bits of each
result in order, modulo `2^64`.  Every power of `digestMul` is odd, so a chunk whose results
differ from Talos's in one result has another digest, and since every term lies below `2^32` and
the order of `digestMul` modulo `2^33` is `2^31`, two errors in the same bit of two results never
cancel.  The program writes the eight bytes of each chunk's digest to the UART, lowest first, so a run of every
word writes 512 KiB for each case, which the UART carries in seconds under KVM.

`image` lays out the header, the startup of `LeanExe.A64.Startup`, which enables floating point
and writes FPCR as the back end's Images do, and the program, which runs each segment, a case and
a range of chunks, in turn.  For the word `i` of X19, the loop sets X2 and X3 as the case's input
says, runs the case's code, which leaves the result in X2, and adds its halves to the digest in
X20.
`expected` computes the digests of a segment's chunks from Talos's functions in parallel tasks,
or from the model's runs of the cases' code, which compute the same functions and check the
cases' oracles on samples, and `check` compares them with the UART's bytes.
-/

namespace TestSupport.A64.Exhaust

open LeanExe.A64 TestSupport.A64.Fp

/-- Where the loop puts the word `i` under test: in X2, with the fixed word in X3; in X3, with the
fixed word in X2; as `i * (2^32 + 1)` in X2; or as `i * 2^32 + 1` in X2. -/
inductive Input where
  | first | second | wide | high
  deriving BEq, Repr

/-- A case: its name, the code that the generator emits for its operation on X2 and X3, which
leaves the result in X2, Talos's function of the operation on the words of X2 and X3, where the
word under test goes, and the fixed word. -/
structure Case where
  name : String
  code : List Instr
  oracle : UInt64 → UInt64 → UInt64
  input : Input := .first
  fixed : UInt64 := 0

/-- The code of the three f32 comparisons of X2 with X3, `f32Eq`, `f32Lt`, and `f32Le`, whose
results form bits 0, 1, and 2 of X2, as `Form.code` gives them for `FCMP`. -/
def cmpCode32 : List Instr :=
  [mov 4 2] ++ fCmp32 1 4 3 ++ [mov 7 2] ++ fCmp32 5 7 3 ++ fCmp32 8 2 3 ++
    [.addReg 2 2 2, .addReg 2 2 7, .addReg 2 2 2, .addReg 2 2 4]

/-- The cases.  `UCVTF` of a 64-bit word takes the word as `i`, `i * (2^32 + 1)`, and
`i * 2^32 + 1`, whose low bit separates a rounding to binary32 from a rounding through binary64.
The binary forms take the word with a fixed operand: `FADD` with 1.0, the smallest subnormal, the
largest finite single, infinity, and 0, `FSUB` of 1.0, `FMUL` by 3.0, the single after 1.0,
2^-24, infinity, and 0, `FDIV` of 1.0 by the word and of the word by 3.0, 2^24, infinity, and 0,
and the comparisons with 1.0 and -0.0.  They give additive cancellation and every alignment of the
exponents, product ties and near ties, subnormal products and their ties, the ties of quotients on
the subnormal grid, product and quotient overflow, and the special results of infinities and
zeros, such as infinity minus infinity, 0 times infinity, 0/0, and infinity over infinity. -/
def cases : List Case :=
  let un (f : UInt32 → UInt32) (a _ : UInt64) : UInt64 := (f a.toUInt32).toUInt64
  let bin (f : UInt32 → UInt32 → UInt32) (a b : UInt64) : UInt64 :=
    (f a.toUInt32 b.toUInt32).toUInt64
  let cmp (a b : UInt64) : UInt64 :=
    let x := a.toUInt32
    let y := b.toUInt32
    (if Wasm.f32Le x y then 4 else 0) + (if Wasm.f32Lt x y then 2 else 0) +
      (if Wasm.f32Eq x y then 1 else 0)
  [ { name := "sqrt", code := unCode32 .fsqrtS 2, oracle := un Wasm.f32Sqrt },
    { name := "nearest", code := unCode32 .frintnS 2, oracle := un Wasm.f32Nearest },
    { name := "abs", code := absCode32 2, oracle := un Wasm.f32Abs },
    { name := "neg", code := fBin32 .fsubS 2 3, oracle := bin Wasm.f32Sub, input := .second,
      fixed := 0x80000000 },
    { name := "ofbits", code := fBin32 .faddS 2 3, oracle := bin Wasm.f32Add,
      fixed := 0x80000000 },
    { name := "scvtf", code := toS32 .scvtfSW 2, oracle := un Wasm.f32ConvertI32S },
    { name := "ucvtf", code := toS32 .ucvtfSX 2,
      oracle := fun a _ => (Wasm.f32ConvertI64U a).toUInt64 },
    { name := "ucvtf-wide", code := toS32 .ucvtfSX 2,
      oracle := fun a _ => (Wasm.f32ConvertI64U a).toUInt64, input := .wide },
    { name := "ucvtf-high", code := toS32 .ucvtfSX 2,
      oracle := fun a _ => (Wasm.f32ConvertI64U a).toUInt64, input := .high },
    { name := "fcvtzu", code := ofS32 .fcvtzuXS 2,
      oracle := fun a _ => Wasm.i64TruncSatF32U a.toUInt32 },
    { name := "fcvtzs", code := ofS32 .fcvtzsWS 2, oracle := un Wasm.i32TruncSatF32S },
    { name := "add-one", code := fBin32 .faddS 2 3, oracle := bin Wasm.f32Add,
      fixed := 0x3F800000 },
    { name := "add-tiny", code := fBin32 .faddS 2 3, oracle := bin Wasm.f32Add,
      fixed := 0x00000001 },
    { name := "add-max", code := fBin32 .faddS 2 3, oracle := bin Wasm.f32Add,
      fixed := 0x7F7FFFFF },
    { name := "add-inf", code := fBin32 .faddS 2 3, oracle := bin Wasm.f32Add,
      fixed := 0x7F800000 },
    { name := "add-zero", code := fBin32 .faddS 2 3, oracle := bin Wasm.f32Add, fixed := 0 },
    { name := "sub-one", code := fBin32 .fsubS 2 3, oracle := bin Wasm.f32Sub,
      fixed := 0x3F800000 },
    { name := "mul-three", code := fBin32 .fmulS 2 3, oracle := bin Wasm.f32Mul,
      fixed := 0x40400000 },
    { name := "mul-next", code := fBin32 .fmulS 2 3, oracle := bin Wasm.f32Mul,
      fixed := 0x3F800001 },
    { name := "mul-tiny", code := fBin32 .fmulS 2 3, oracle := bin Wasm.f32Mul,
      fixed := 0x33800000 },
    { name := "mul-inf", code := fBin32 .fmulS 2 3, oracle := bin Wasm.f32Mul,
      fixed := 0x7F800000 },
    { name := "mul-zero", code := fBin32 .fmulS 2 3, oracle := bin Wasm.f32Mul, fixed := 0 },
    { name := "div-recip", code := fBin32 .fdivS 2 3, oracle := bin Wasm.f32Div,
      input := .second, fixed := 0x3F800000 },
    { name := "div-three", code := fBin32 .fdivS 2 3, oracle := bin Wasm.f32Div,
      fixed := 0x40400000 },
    { name := "div-big", code := fBin32 .fdivS 2 3, oracle := bin Wasm.f32Div,
      fixed := 0x4B800000 },
    { name := "div-inf", code := fBin32 .fdivS 2 3, oracle := bin Wasm.f32Div,
      fixed := 0x7F800000 },
    { name := "div-zero", code := fBin32 .fdivS 2 3, oracle := bin Wasm.f32Div, fixed := 0 },
    { name := "cmp-one", code := cmpCode32, oracle := cmp, fixed := 0x3F800000 },
    { name := "cmp-zero", code := cmpCode32, oracle := cmp, fixed := 0x80000000 } ]

def caseOf (s : String) : Option Case := cases.find? (·.name == s)

/-- A case whose operation takes two operands, one of them fixed. -/
def Case.binary (c : Case) : Bool := c.name.startsWith "add" || c.name.startsWith "sub" ||
  c.name.startsWith "mul" || c.name.startsWith "div" || c.name.startsWith "cmp"

/-- The words of X2 and X3 for the word `i`. -/
def Case.operands (c : Case) (i : UInt64) : UInt64 × UInt64 :=
  match c.input with
  | .first => (i, c.fixed)
  | .second => (c.fixed, i)
  | .wide => (i <<< 32 ||| i, c.fixed)
  | .high => (i <<< 32 ||| 1, c.fixed)

/-- X2 after the model runs the case's code on the word `i`. -/
def Case.model (c : Case) (i : UInt64) : Option UInt64 := do
  let (a, b) := c.operands i
  let s : State :=
    { regs := fun r => if r.val = 2 then a else if r.val = 3 then b else 0, dregs := fun _ => 0,
      sp := 0, pc := 0, nFlag := false, zFlag := false, cFlag := false, vFlag := false,
      mem := fun _ => 0, out := [] }
  let P : Platform := { normal := fun _ => false, uart := uartAddr }
  let t ← c.code.foldlM (fun s i => exec P i s) s
  return t.regs 2

/-- The multiplier of the digest. -/
def digestMul : UInt64 := 0x9E3779B97F4A7C15

/-- The words of a chunk. -/
def chunkBits : Nat := 16

/-- A segment of a run: a case and its chunks from `start`, `count` of them. -/
structure Segment where
  case : Case
  start : Nat
  count : Nat

/-- The stores of the eight bytes of X20 to the UART at X23, lowest first, which leave X20 0. -/
def emitDigest : List Instr :=
  (List.range 8).flatMap fun _ => [Instr.strb 20 23 0, .lsrImm 20 20 8]

/-- The loop of the segment `g` placed at `a`: X19 from the segment's first word, X25 at the word
after its last, and for each word the operands, the case's code, and the digest; after each chunk
the digest goes to the UART. -/
def segmentCode (a : UInt64) (g : Segment) : GenM (List Instr) := do
  let first := UInt64.ofNat (g.start * 2 ^ chunkBits)
  let last := UInt64.ofNat ((g.start + g.count) * 2 ^ chunkBits)
  let setup := movImm 19 first ++ movImm 25 last ++ [Instr.movz 20 0 0]
  let head := after a setup.length
  let ins : List Instr := match g.case.input with
    | .first => [mov 2 19] ++ movImm 3 g.case.fixed
    | .second => movImm 2 g.case.fixed ++ [mov 3 19]
    | .wide => [.lslv 2 19 26, .orrReg 2 2 19] ++ movImm 3 g.case.fixed
    | .high => [.lslv 2 19 26, .orrReg 2 2 28] ++ movImm 3 g.case.fixed
  let fold := [Instr.orrW 27 31 2, .madd 20 20 21 27, .lsrImm 27 2 32, .madd 20 20 21 27]
  let body := ins ++ g.case.code ++ fold ++ [.addImm 19 19 1, .andReg 24 19 22]
  let inner ← cbField (after head body.length) head
  let tail := emitDigest ++ [.subsReg 31 19 25]
  let back ← cbField (after head (body.length + 1 + tail.length)) head
  return setup ++ body ++ [.cbnz 24 inner] ++ tail ++ [.bcond 1 back]

/-- The program at `main`: X23 at the UART, X21 at `digestMul`, X22 at the mask of a chunk's
offset, X26 at 32, X28 at 1, the loop of each segment, and X0 at 0 and `RET` to the exit. -/
def mainCode (main : UInt64) (segs : List Segment) : GenM (List Instr) := do
  let mut code := movImm 23 uartAddr ++ movImm 21 digestMul ++
    movImm 22 (UInt64.ofNat (2 ^ chunkBits - 1)) ++ movImm 26 32 ++ movImm 28 1
  for g in segs do
    code := code ++ (← segmentCode (after main code.length) g)
  return code ++ [.movz 0 0 0, .ret 30]

/-- The Image of the segments `segs`. -/
def image (segs : List Segment) : GenM ByteArray := do
  if segs.any fun g => g.count = 0 ∨ 2 ^ (32 - chunkBits) < g.start + g.count then
    throw "a segment without chunks or beyond the 32-bit words"
  return (← imageWith (fun main => mainCode main segs) ByteArray.empty).1

/-- The digest `h` updated by the halves of the result `r`. -/
def foldResult (h r : UInt64) : UInt64 :=
  (h * digestMul + (r &&& (0xFFFFFFFF : UInt64))) * digestMul + (r >>> (32 : UInt64))

/-- The digest of chunk `k` of case `c`: of the results of Talos's function, or with `model` of
the model's runs of the case's code, or the first word on which the model stops. -/
def chunkDigest (c : Case) (model : Bool) (k : Nat) : Except UInt64 UInt64 := do
  let mut h : UInt64 := 0
  for j in [0:2 ^ chunkBits] do
    let i := UInt64.ofNat (k * 2 ^ chunkBits + j)
    if model then
      match c.model i with
      | some r => h := foldResult h r
      | none => throw i
    else
      let (a, b) := c.operands i
      h := foldResult h (c.oracle a b)
  return h

/-- The digests of the chunks `ks` of case `c`, of Talos's function or with `model` of the model,
computed in `tasks` parallel tasks, of which task `t` takes the chunks at the positions `t`,
`t + tasks`, and so on, so that each task meets chunks of every part of the range. -/
def expected (c : Case) (ks : Array Nat) (model : Bool) (tasks : Nat) :
    Except String (Array UInt64) := do
  let T := max tasks 1
  let ts := (List.range T).toArray.map fun t =>
    Task.spawn fun _ =>
      (List.range ((ks.size + T - 1 - t) / T)).toArray.mapM fun j =>
        chunkDigest c model ks[t + j * T]!
  let mut parts := #[]
  for t in ts do
    match t.get with
    | .ok ds => parts := parts.push ds
    | .error i => throw s!"the model stops on {c.name} of word {i}"
  return (List.range ks.size).toArray.map fun i => parts[i % T]![i / T]!

/-- The digest at chunk `k` of the UART's bytes. -/
def digestAt (out : ByteArray) (k : Nat) : UInt64 := get64 out (8 * k)

end TestSupport.A64.Exhaust
