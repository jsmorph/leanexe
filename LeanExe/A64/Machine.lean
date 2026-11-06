import Interpreter.Wasm.Float

/-!
A model of the AArch64 instructions that the native back end emits, for a bare-metal program at
exception level 1 under the startup code of `tools/baremetal/start.S`.  It covers the integer forms
that the back end emits and the double-precision forms that Wasm's f64 arithmetic needs.

The code lies in a fixed map from addresses to 32-bit words, which the theorem derives from the
image's bytes, so a store never changes what the processor fetches.  `step` fetches the word at
the program counter, decodes it, and executes it.  It returns `none` for a word outside the
forms, for an access to memory that `Platform.normal` does not cover, for a load or store based on
the stack pointer while the stack pointer is not a multiple of 16, and for every access to the
UART other than a byte store to its data register, so a theorem about a run that never stops the
model excludes the faults of those accesses.  The flags, the stack pointer, and the semantics of
register 31 follow the pseudocode of the Arm Architecture Reference Manual (DDI 0487): register 31
is the stack pointer as the base of a load or store and as an operand or destination of `ADD` and
`SUB` with an immediate, and the zero register elsewhere.  Unaligned accesses to Normal memory
succeed, as they do while `SCTLR_EL1.A` is clear.

The floating-point registers D0 to D31 hold the 64-bit words of doubles.  The arithmetic forms on
them compute Talos's IEEE 754 functions of `Interpreter/Wasm/Float.lean`, which round to nearest,
keep subnormals, and give the canonical NaN `0x7FF8000000000000` for every NaN result.  The
processor computes the same with `FPCR` as the startup code sets it under `DEFAULT_NAN`: `DN`
set, `FZ` clear, and rounding to nearest, which the co-simulation checks.
-/

namespace LeanExe.A64

/-- Where loads and stores may go.  `normal a` holds when the byte at `a` is mapped as Normal
memory, and `uart` is the address of the UART's data register, where a byte store appends the
byte to the output. -/
structure Platform where
  normal : UInt64 → Bool
  uart : UInt64

/-- The state that the emitted code uses: the general registers X0 to X30, the floating-point
registers D0 to D31, the stack pointer, the program counter, the condition flags, the memory as
bytes, and the bytes written to the UART. -/
structure State where
  regs : Fin 31 → UInt64
  dregs : Fin 32 → UInt64
  sp : UInt64
  pc : UInt64
  nFlag : Bool
  zFlag : Bool
  cFlag : Bool
  vFlag : Bool
  mem : UInt64 → UInt8
  out : List UInt8

/-- The instruction forms of the model, all with 64-bit registers but `orrW`.  A register field is
the 5-bit number of the encoding, and an immediate field is the encoding's unsigned field. -/
inductive Instr where
  /-- `MOVZ Xd, #imm, LSL #(16 * hw)`. -/
  | movz (d : Fin 32) (imm : Fin 65536) (hw : Fin 4)
  /-- `MOVK Xd, #imm, LSL #(16 * hw)`. -/
  | movk (d : Fin 32) (imm : Fin 65536) (hw : Fin 4)
  /-- `ADD Xd|SP, Xn|SP, #imm`. -/
  | addImm (d n : Fin 32) (imm : Fin 4096)
  /-- `SUB Xd|SP, Xn|SP, #imm`. -/
  | subImm (d n : Fin 32) (imm : Fin 4096)
  /-- `SUBS Xd, Xn|SP, #imm`, which is `CMP Xn, #imm` when `d` is 31. -/
  | subsImm (d n : Fin 32) (imm : Fin 4096)
  /-- `SUBS Xd, Xn, Xm`, which is `CMP Xn, Xm` when `d` is 31. -/
  | subsReg (d n m : Fin 32)
  /-- `CSINC Xd, Xn, Xm, cond`, which is `CSET Xd, c` when `n` and `m` are 31 and `cond` is the
  inverse of `c`. -/
  | csinc (d n m : Fin 32) (cond : Fin 16)
  /-- `ORR Xd, Xn, Xm`, which is `MOV Xd, Xm` when `n` is 31. -/
  | orrReg (d n m : Fin 32)
  /-- `LSR Xd, Xn, #sh`, an alias of `UBFM Xd, Xn, #sh, #63`. -/
  | lsrImm (d n : Fin 32) (sh : Fin 64)
  /-- `LDR Xt, [Xn|SP, #(8 * imm)]`. -/
  | ldr (t n : Fin 32) (imm : Fin 4096)
  /-- `STR Xt, [Xn|SP, #(8 * imm)]`. -/
  | str (t n : Fin 32) (imm : Fin 4096)
  /-- `STRB Wt, [Xn|SP, #imm]`. -/
  | strb (t n : Fin 32) (imm : Fin 4096)
  /-- `B` to the program counter plus 4 times `imm` read as a signed 26-bit number. -/
  | b (imm : Fin 67108864)
  /-- `BL` to the program counter plus 4 times `imm` read as a signed 26-bit number. -/
  | bl (imm : Fin 67108864)
  /-- `CBZ Xt` to the program counter plus 4 times `imm` read as a signed 19-bit number. -/
  | cbz (t : Fin 32) (imm : Fin 524288)
  /-- `CBNZ Xt` to the program counter plus 4 times `imm` read as a signed 19-bit number. -/
  | cbnz (t : Fin 32) (imm : Fin 524288)
  /-- `RET Xn`. -/
  | ret (n : Fin 32)
  /-- `UDIV Xd, Xn, Xm`. -/
  | udiv (d n m : Fin 32)
  /-- `MSUB Xd, Xn, Xm, Xa`, which computes `Xa - Xn * Xm`. -/
  | msub (d n m a : Fin 32)
  /-- `ADD Xd, Xn, Xm`. -/
  | addReg (d n m : Fin 32)
  /-- `SUB Xd, Xn, Xm`. -/
  | subReg (d n m : Fin 32)
  /-- `AND Xd, Xn, Xm`. -/
  | andReg (d n m : Fin 32)
  /-- `EOR Xd, Xn, Xm`. -/
  | eorReg (d n m : Fin 32)
  /-- `MADD Xd, Xn, Xm, Xa`, which computes `Xa + Xn * Xm` and is `MUL Xd, Xn, Xm` when `a` is
  31. -/
  | madd (d n m a : Fin 32)
  /-- `LSLV Xd, Xn, Xm`, a shift left by `Xm` modulo 64. -/
  | lslv (d n m : Fin 32)
  /-- `LSRV Xd, Xn, Xm`, a logical shift right by `Xm` modulo 64. -/
  | lsrv (d n m : Fin 32)
  /-- `ORR Wd, Wn, Wm`, which writes the 32-bit result zero-extended and is `MOV Wd, Wm` when `n`
  is 31. -/
  | orrW (d n m : Fin 32)
  /-- `B.cond` to the program counter plus 4 times `imm` read as a signed 19-bit number when the
  condition `cond` holds. -/
  | bcond (cond : Fin 16) (imm : Fin 524288)
  /-- `FMOV Dd, Xn`, which copies the word of `Xn`, the zero register for 31, to `Dd`. -/
  | fmovDX (d n : Fin 32)
  /-- `FMOV Xd, Dn`, which copies the word of `Dn` to `Xd`. -/
  | fmovXD (d n : Fin 32)
  /-- `FADD Dd, Dn, Dm`. -/
  | fadd (d n m : Fin 32)
  /-- `FSUB Dd, Dn, Dm`, which computes `Dn - Dm`. -/
  | fsub (d n m : Fin 32)
  /-- `FMUL Dd, Dn, Dm`. -/
  | fmul (d n m : Fin 32)
  /-- `FDIV Dd, Dn, Dm`, which computes `Dn / Dm`. -/
  | fdiv (d n m : Fin 32)
  /-- `FSQRT Dd, Dn`. -/
  | fsqrt (d n : Fin 32)
  /-- `FABS Dd, Dn`. -/
  | fabs (d n : Fin 32)
  /-- `UCVTF Dd, Xn`, which converts the unsigned word of `Xn` to a double. -/
  | ucvtf (d n : Fin 32)
  deriving DecidableEq, Repr

/-- The instruction that the 32-bit word of value `v` encodes, or `none` for a word outside the
forms.  The fixed bits and the fields are those of the A64 encodings in the Arm Architecture
Reference Manual. -/
def decodeNat (v : Nat) : Option Instr :=
  let d : Fin 32 := ⟨v % 32, Nat.mod_lt _ (by decide)⟩
  let n : Fin 32 := ⟨v / 32 % 32, Nat.mod_lt _ (by decide)⟩
  let m : Fin 32 := ⟨v / 65536 % 32, Nat.mod_lt _ (by decide)⟩
  let a : Fin 32 := ⟨v / 1024 % 32, Nat.mod_lt _ (by decide)⟩
  let imm12 : Fin 4096 := ⟨v / 1024 % 4096, Nat.mod_lt _ (by decide)⟩
  let imm16 : Fin 65536 := ⟨v / 32 % 65536, Nat.mod_lt _ (by decide)⟩
  let hw : Fin 4 := ⟨v / 2097152 % 4, Nat.mod_lt _ (by decide)⟩
  let cond : Fin 16 := ⟨v / 4096 % 16, Nat.mod_lt _ (by decide)⟩
  let imm26 : Fin 67108864 := ⟨v % 67108864, Nat.mod_lt _ (by decide)⟩
  let imm19 : Fin 524288 := ⟨v / 32 % 524288, Nat.mod_lt _ (by decide)⟩
  let sh : Fin 64 := ⟨v / 65536 % 64, Nat.mod_lt _ (by decide)⟩
  if v / 8388608 = 0x1A5 then some (.movz d imm16 hw)
  else if v / 8388608 = 0x1E5 then some (.movk d imm16 hw)
  else if v / 4194304 = 0x244 then some (.addImm d n imm12)
  else if v / 4194304 = 0x344 then some (.subImm d n imm12)
  else if v / 4194304 = 0x3C4 then some (.subsImm d n imm12)
  else if v / 2097152 = 0x4D4 ∧ v / 1024 % 4 = 1 then some (.csinc d n m cond)
  else if v / 2097152 = 0x758 ∧ v / 1024 % 64 = 0 then some (.subsReg d n m)
  else if v / 2097152 = 0x550 ∧ v / 1024 % 64 = 0 then some (.orrReg d n m)
  else if v / 4194304 = 0x34D ∧ v / 1024 % 64 = 63 then some (.lsrImm d n sh)
  else if v / 4194304 = 0x3E5 then some (.ldr d n imm12)
  else if v / 4194304 = 0x3E4 then some (.str d n imm12)
  else if v / 4194304 = 0xE4 then some (.strb d n imm12)
  else if v / 67108864 = 0x5 then some (.b imm26)
  else if v / 67108864 = 0x25 then some (.bl imm26)
  else if v / 16777216 = 0xB4 then some (.cbz d imm19)
  else if v / 16777216 = 0xB5 then some (.cbnz d imm19)
  else if v / 1024 = 0x3597C0 ∧ v % 32 = 0 then some (.ret n)
  else if v / 2097152 = 0x4D6 ∧ v / 1024 % 64 = 2 then some (.udiv d n m)
  else if v / 2097152 = 0x4D8 ∧ v / 32768 % 2 = 1 then some (.msub d n m a)
  else if v / 2097152 = 0x458 ∧ v / 1024 % 64 = 0 then some (.addReg d n m)
  else if v / 2097152 = 0x658 ∧ v / 1024 % 64 = 0 then some (.subReg d n m)
  else if v / 2097152 = 0x450 ∧ v / 1024 % 64 = 0 then some (.andReg d n m)
  else if v / 2097152 = 0x650 ∧ v / 1024 % 64 = 0 then some (.eorReg d n m)
  else if v / 2097152 = 0x4D8 ∧ v / 32768 % 2 = 0 then some (.madd d n m a)
  else if v / 2097152 = 0x4D6 ∧ v / 1024 % 64 = 8 then some (.lslv d n m)
  else if v / 2097152 = 0x4D6 ∧ v / 1024 % 64 = 9 then some (.lsrv d n m)
  else if v / 2097152 = 0x150 ∧ v / 1024 % 64 = 0 then some (.orrW d n m)
  else if v / 16777216 = 0x54 ∧ v / 16 % 2 = 0 then
    some (.bcond ⟨v % 16, Nat.mod_lt _ (by decide)⟩ imm19)
  else if v / 1024 = 0x2799C0 then some (.fmovDX d n)
  else if v / 1024 = 0x279980 then some (.fmovXD d n)
  else if v / 2097152 = 0xF3 ∧ v / 1024 % 64 = 10 then some (.fadd d n m)
  else if v / 2097152 = 0xF3 ∧ v / 1024 % 64 = 14 then some (.fsub d n m)
  else if v / 2097152 = 0xF3 ∧ v / 1024 % 64 = 2 then some (.fmul d n m)
  else if v / 2097152 = 0xF3 ∧ v / 1024 % 64 = 6 then some (.fdiv d n m)
  else if v / 1024 = 0x79870 then some (.fsqrt d n)
  else if v / 1024 = 0x79830 then some (.fabs d n)
  else if v / 1024 = 0x2798C0 then some (.ucvtf d n)
  else none

/-- The instruction that the word `w` encodes, or `none` for a word outside the forms. -/
def decode (w : UInt32) : Option Instr :=
  decodeNat w.toNat

namespace State

/-- Register `r`, where 31 reads as zero. -/
def x (s : State) (r : Fin 32) : UInt64 :=
  if h : r.val < 31 then s.regs ⟨r.val, h⟩ else 0

/-- Register `r`, where 31 reads as the stack pointer. -/
def xsp (s : State) (r : Fin 32) : UInt64 :=
  if h : r.val < 31 then s.regs ⟨r.val, h⟩ else s.sp

/-- The state with register `r` set to `v`, where a write to 31 has no effect. -/
def setX (s : State) (r : Fin 32) (v : UInt64) : State :=
  if r.val < 31 then { s with regs := fun i => if i.val = r.val then v else s.regs i } else s

/-- The state with the floating-point register `r` set to the word `v`. -/
def setD (s : State) (r : Fin 32) (v : UInt64) : State :=
  { s with dregs := fun i => if i = r then v else s.dregs i }

/-- The state with register `r` set to `v`, where 31 is the stack pointer. -/
def setXsp (s : State) (r : Fin 32) (v : UInt64) : State :=
  if r.val < 31 then { s with regs := fun i => if i.val = r.val then v else s.regs i }
  else { s with sp := v }

/-- `ConditionHolds` of the Arm Architecture Reference Manual for the condition `cond`. -/
def condHolds (s : State) (cond : Fin 16) : Bool :=
  let r := match cond.val / 2 with
    | 0 => s.zFlag
    | 1 => s.cFlag
    | 2 => s.nFlag
    | 3 => s.vFlag
    | 4 => s.cFlag && !s.zFlag
    | 5 => s.nFlag == s.vFlag
    | 6 => s.nFlag == s.vFlag && !s.zFlag
    | _ => true
  if cond.val % 2 = 1 ∧ cond.val ≠ 15 then !r else r

/-- The state after `SUBS` writes `a - b` to register `d`, with the flags of
`AddWithCarry(a, NOT b, 1)`: N is the result's top bit, Z its being zero, C the absence of a
borrow, and V a signed overflow. -/
def subs (s : State) (d : Fin 32) (a b : UInt64) : State :=
  let r := a - b
  { s.setX d r with
    nFlag := r >>> 63 == 1, zFlag := r == 0, cFlag := b ≤ a,
    vFlag := ((a ^^^ b) &&& (a ^^^ r)) >>> 63 == 1 }

/-- A load or store based on register `n` passes the stack pointer's alignment check: the base
is not the stack pointer, or the stack pointer is a multiple of 16. -/
def spAligned (s : State) (n : Fin 32) : Bool :=
  n.val != 31 || s.sp % 16 == 0

end State

/-- The field `v` of `bits` bits read as a two's complement number, as a 64-bit word. -/
def sext (bits v : Nat) : UInt64 :=
  if v < 2 ^ (bits - 1) then UInt64.ofNat v else UInt64.ofNat v - UInt64.ofNat (2 ^ bits)

/-- The eight bytes from `a`, the lowest first, as a word. -/
def load64 (m : UInt64 → UInt8) (a : UInt64) : UInt64 :=
  (m a).toUInt64 ||| (m (a + 1)).toUInt64 <<< 8 ||| (m (a + 2)).toUInt64 <<< 16 |||
    (m (a + 3)).toUInt64 <<< 24 ||| (m (a + 4)).toUInt64 <<< 32 |||
    (m (a + 5)).toUInt64 <<< 40 ||| (m (a + 6)).toUInt64 <<< 48 |||
    (m (a + 7)).toUInt64 <<< 56

/-- The memory `m` with the eight bytes from `a` replaced by those of `v`, the lowest first. -/
def store64 (m : UInt64 → UInt8) (a v : UInt64) : UInt64 → UInt8 :=
  fun b => if b - a < 8 then (v >>> ((b - a) * 8)).toUInt8 else m b

/-- The memory `m` with the byte at `a` replaced by `v`. -/
def store8 (m : UInt64 → UInt8) (a : UInt64) (v : UInt8) : UInt64 → UInt8 :=
  fun b => if b = a then v else m b

/-- Every one of the `k` bytes from `a` is Normal memory. -/
def Platform.mapped (P : Platform) (a : UInt64) (k : Nat) : Bool :=
  (List.range k).all fun i => P.normal (a + UInt64.ofNat i)

/-- The state after the instruction `i` at the program counter, or `none` when it faults. -/
def exec (P : Platform) (i : Instr) (s : State) : Option State :=
  let next := s.pc + 4
  match i with
  | .movz d imm hw =>
      some { s.setX d (UInt64.ofNat imm.val <<< UInt64.ofNat (16 * hw.val)) with pc := next }
  | .movk d imm hw =>
      let sh := UInt64.ofNat (16 * hw.val)
      let w := (s.x d &&& ~~~((0xFFFF : UInt64) <<< sh)) ||| UInt64.ofNat imm.val <<< sh
      some { s.setX d w with pc := next }
  | .addImm d n imm => some { s.setXsp d (s.xsp n + UInt64.ofNat imm.val) with pc := next }
  | .subImm d n imm => some { s.setXsp d (s.xsp n - UInt64.ofNat imm.val) with pc := next }
  | .subsImm d n imm => some { s.subs d (s.xsp n) (UInt64.ofNat imm.val) with pc := next }
  | .subsReg d n m => some { s.subs d (s.x n) (s.x m) with pc := next }
  | .csinc d n m cond =>
      some { s.setX d (if s.condHolds cond then s.x n else s.x m + 1) with pc := next }
  | .orrReg d n m => some { s.setX d (s.x n ||| s.x m) with pc := next }
  | .lsrImm d n sh => some { s.setX d (s.x n >>> UInt64.ofNat sh.val) with pc := next }
  | .ldr t n imm =>
      let a := s.xsp n + UInt64.ofNat (8 * imm.val)
      if s.spAligned n && P.mapped a 8 then some { s.setX t (load64 s.mem a) with pc := next }
      else none
  | .str t n imm =>
      let a := s.xsp n + UInt64.ofNat (8 * imm.val)
      if s.spAligned n && P.mapped a 8 then
        some { s with mem := store64 s.mem a (s.x t), pc := next }
      else none
  | .strb t n imm =>
      let a := s.xsp n + UInt64.ofNat imm.val
      let v := (s.x t).toUInt8
      if !s.spAligned n then none
      else if a = P.uart then some { s with out := s.out ++ [v], pc := next }
      else if P.normal a then some { s with mem := store8 s.mem a v, pc := next }
      else none
  | .b imm => some { s with pc := s.pc + sext 26 imm.val * 4 }
  | .bl imm => some { s.setX 30 next with pc := s.pc + sext 26 imm.val * 4 }
  | .cbz t imm =>
      some { s with pc := if s.x t = 0 then s.pc + sext 19 imm.val * 4 else next }
  | .cbnz t imm =>
      some { s with pc := if s.x t ≠ 0 then s.pc + sext 19 imm.val * 4 else next }
  | .ret n => some { s with pc := s.x n }
  | .udiv d n m => some { s.setX d (s.x n / s.x m) with pc := next }
  | .msub d n m a => some { s.setX d (s.x a - s.x n * s.x m) with pc := next }
  | .addReg d n m => some { s.setX d (s.x n + s.x m) with pc := next }
  | .subReg d n m => some { s.setX d (s.x n - s.x m) with pc := next }
  | .andReg d n m => some { s.setX d (s.x n &&& s.x m) with pc := next }
  | .eorReg d n m => some { s.setX d (s.x n ^^^ s.x m) with pc := next }
  | .madd d n m a => some { s.setX d (s.x a + s.x n * s.x m) with pc := next }
  | .lslv d n m => some { s.setX d (s.x n <<< (s.x m % 64)) with pc := next }
  | .lsrv d n m => some { s.setX d (s.x n >>> (s.x m % 64)) with pc := next }
  | .orrW d n m => some { s.setX d (s.x n ||| s.x m).toUInt32.toUInt64 with pc := next }
  | .bcond cond imm =>
      some { s with pc := if s.condHolds cond then s.pc + sext 19 imm.val * 4 else next }
  | .fmovDX d n => some { s.setD d (s.x n) with pc := next }
  | .fmovXD d n => some { s.setX d (s.dregs n) with pc := next }
  | .fadd d n m => some { s.setD d (Wasm.f64Add (s.dregs n) (s.dregs m)) with pc := next }
  | .fsub d n m => some { s.setD d (Wasm.f64Sub (s.dregs n) (s.dregs m)) with pc := next }
  | .fmul d n m => some { s.setD d (Wasm.f64Mul (s.dregs n) (s.dregs m)) with pc := next }
  | .fdiv d n m => some { s.setD d (Wasm.f64Div (s.dregs n) (s.dregs m)) with pc := next }
  | .fsqrt d n => some { s.setD d (Wasm.f64Sqrt (s.dregs n)) with pc := next }
  | .fabs d n => some { s.setD d (Wasm.f64Abs (s.dregs n)) with pc := next }
  | .ucvtf d n => some { s.setD d (Wasm.f64ConvertI64U (s.x n)) with pc := next }

/-- One step from `s` with the code `code`: the fetch, the decoding, and the execution of the
word at the program counter. -/
def step (P : Platform) (code : UInt64 → Option UInt32) (s : State) : Option State := do
  let w ← code s.pc
  let i ← decode w
  exec P i s

/-- `k` steps from `s`, or `none` when a step stops the model. -/
def run (P : Platform) (code : UInt64 → Option UInt32) : Nat → State → Option State
  | 0, s => some s
  | k + 1, s => (step P code s).bind (run P code k)

end LeanExe.A64
