import LeanExe.A64.Encode

/-!
The GNU assembler's syntax for the loads `LDR Wt` and `LDRB` of the AArch64 model of
`LeanExe/A64/Machine.lean`, and their samples, which `tests/baremetal/a64-encode.sh` assembles
with `as`.  The samples set `Rt` to 0, 9, 30, and 31, `Rn` to 0, 8, 30, and 31, and the immediate
field to 0, 1, 6, and 4095, so that register 31 takes each role, as `WZR` for `Rt` and `SP` for
`Rn`, and the immediate takes its limits.
-/

namespace TestSupport.A64

open LeanExe.A64

/-- The 32-bit name of register `r` of a load's destination, with `WZR` for 31. -/
def wreg (r : Fin 32) : String := if r.val = 31 then "wzr" else s!"w{r.val}"

/-- The 64-bit name of register `r` of a load's base, with `SP` for 31. -/
def xsp (r : Fin 32) : String := if r.val = 31 then "sp" else s!"x{r.val}"

/-- The instruction in the GNU assembler's syntax, for the forms of the comparison. -/
def asm? : Instr → Option String
  | .ldrW t n imm => some s!"ldr {wreg t}, [{xsp n}, #{4 * imm.val}]"
  | .ldrb t n imm => some s!"ldrb {wreg t}, [{xsp n}, #{imm.val}]"
  | _ => none

/-- The name of the instruction's form, for the forms of the comparison. -/
def formName : Instr → String
  | .ldrW .. => "ldrW"
  | .ldrb .. => "ldrb"
  | _ => "other"

/-- The samples of `LDR Wt` and `LDRB`. -/
def samples : List Instr := Id.run do
  let mut out := []
  for t in [(0 : Fin 32), 9, 30, 31] do
    for n in [(0 : Fin 32), 8, 30, 31] do
      for i in [(0 : Fin 4096), 1, 6, 4095] do
        out := out ++ [Instr.ldrW t n i, Instr.ldrb t n i]
  return out

/-- The assembly of the samples, one instruction per line. -/
def samplesAsm : String :=
  ".text\n" ++ String.join (samples.filterMap fun i => (asm? i).map fun s => s!"  {s}\n")

/-- The differences between the assembler's bytes `bin` and the encoder's words of the samples,
each word the lowest byte first, and between each of the assembler's words and its decoding. -/
def checkBytes (bin : ByteArray) : List String := Id.run do
  let mut diffs := []
  if bin.size != 4 * samples.length then
    diffs := diffs ++ [s!"{bin.size} bytes for {samples.length} samples"]
  for (i, k) in samples.zipIdx do
    if 4 * k + 4 ≤ bin.size then
      let w : UInt32 := bin[4 * k]!.toUInt32 ||| (bin[4 * k + 1]!.toUInt32 <<< 8) |||
        (bin[4 * k + 2]!.toUInt32 <<< 16) ||| (bin[4 * k + 3]!.toUInt32 <<< 24)
      let line := (asm? i).getD ""
      if w != encode i then
        diffs := diffs ++
          [s!"{line}: the assembler's word {w.toNat}, the encoder's {(encode i).toNat}"]
      if decode w != some i then
        diffs := diffs ++ [s!"{line}: the assembler's word {w.toNat} decodes to another form"]
  return diffs

end TestSupport.A64
