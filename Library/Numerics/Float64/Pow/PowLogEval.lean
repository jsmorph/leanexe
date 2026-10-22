import Library.Numerics.Float64.Pow.PowLogSums
import Library.Numerics.Float64.Pow.PowExpPaths

/-!
The error of `PowLogBits.finalOf` on words.  With `r = z invc - 1` exact (`PowLogReduce`),
`t1 = k ln2hi + logc` exact, `lo2` and `lo4` the exact errors of `t2 = t1 + r` and
`hi = t2 + arhi2` (`PowLogSum.grid_sum`), and `arhi2 = -rhi ^ 2 / 2` exact, the pair
`y + tail` approximates `M = k (ln2hi + ln2lo) + logc + logctail + r - r ^ 2 / 2 + poly r`.  The
remaining errors come from `lo1`, `lo3`, `p`, the sum `lo`, and the final pair, each a small
multiple of the unit roundoff times `|k| 2 ^ -44 + |logctail|`, `|rlo| |r + rhi|`, `|r| ^ 3`,
or the unit roundoff times `|t1 + r|` and `rhi ^ 2`.
-/

namespace Library.Numerics.Float64.Pow.PowLogEval
open CodeLib.IEEE64 LeanExe.ProofKit Library.Numerics.Float64.Exp.ExpSpecialNegative

set_option exponentiation.threshold 4096

/-- `PowLogBits.finalOf` on words. -/
def logWords (iz kd invc lc lt : UInt64) : UInt64 × UInt64 :=
  let zhi := PowLogBits.zhiOf iz
  let zlo := Wasm.IEEE64.sub iz zhi
  let rhi := Wasm.IEEE64.sub (Wasm.IEEE64.mul zhi invc) one
  let rlo := Wasm.IEEE64.mul zlo invc
  let r := Wasm.IEEE64.add rhi rlo
  let t1 := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3FE62E42FEFA3800) lc
  let t2 := Wasm.IEEE64.add t1 r
  let lo1 := Wasm.IEEE64.add (Wasm.IEEE64.mul kd 0x3D2EF35793C76730) lt
  let lo2 := Wasm.IEEE64.add (Wasm.IEEE64.sub t1 t2) r
  let ar := Wasm.IEEE64.mul 0xBFE0000000000000 r
  let arhi := Wasm.IEEE64.mul 0xBFE0000000000000 rhi
  let arhi2 := Wasm.IEEE64.mul rhi arhi
  let hi := Wasm.IEEE64.add t2 arhi2
  let lo3 := Wasm.IEEE64.mul rlo (Wasm.IEEE64.add ar arhi)
  let lo4 := Wasm.IEEE64.add (Wasm.IEEE64.sub t2 hi) arhi2
  let p := PowLogPoly.pWord r ar
  let lo := Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add (Wasm.IEEE64.add lo1 lo2) lo3) lo4) p
  let y := Wasm.IEEE64.add hi lo
  (y, Wasm.IEEE64.add (Wasm.IEEE64.sub hi y) lo)

theorem finalOf_bits (iz : UInt64) (kd invc logc logctail : Float) (hzf : Finite iz)
    (hhf : Finite (PowLogBits.zhiOf iz)) :
    (PowLogBits.finalOf iz kd invc logc logctail).1.toBits =
        (logWords iz kd.toBits invc.toBits logc.toBits logctail.toBits).1 ∧
      (PowLogBits.finalOf iz kd invc logc logctail).2.toBits =
        (logWords iz kd.toBits invc.toBits logc.toBits logctail.toBits).2 := by
  have c : ∀ w : UInt64, Finite w → (Float.ofBits w).toBits = w := fun w hw =>
    PowExpPaths.ofBits_finite w hw
  have fin : ∀ w : UInt64, Wasm.IEEE64.isFinite w = true → Finite w := fun _ h => h
  simp only [PowLogBits.finalOf, logWords, PowLogPoly.pWord, F64Bits.toBits_add,
    F64Bits.toBits_sub, F64Bits.toBits_mul, one_bits, c iz hzf, c _ hhf,
    c 0x3FE62E42FEFA3800 (fin _ (by decide)), c 0x3D2EF35793C76730 (fin _ (by decide)),
    c 0xBFE0000000000000 (fin _ (by decide)), c 0xBFE5555555555560 (fin _ (by decide)),
    c 0x3FE0000000000006 (fin _ (by decide)), c 0x3FE999999959554E (fin _ (by decide)),
    c 0xBFE555555529A47A (fin _ (by decide)), c 0xBFF2495B9B4845E9 (fin _ (by decide)),
    c 0x3FF0002B8B263FC3 (fin _ (by decide))]
  refine ⟨?_, ?_⟩ <;> first | rfl | trivial

#print axioms finalOf_bits

end Library.Numerics.Float64.Pow.PowLogEval
