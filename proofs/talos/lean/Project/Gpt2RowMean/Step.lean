import Project.Gpt2RowMean.Program
import Project.Gpt2RowMean.Source
import Project.ProofKit.PackedWordRead
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2RowMean

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func1[12]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

theorem emitted_loop :
    func1 = func1.take 12 ++ RangeFoldLoop.program 16 17 stepCode ++ func1.drop 13 := rfl

def Accumulator (ptr : UInt64) (input : ByteArray) (row index : Nat) (frame : Locals) : Prop :=
  frame.params = [.i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat row)] ∧
  frame.locals.length = 24 ∧
  frame.locals[1]? = some (.i64 (sumPrefix input row index).toUInt64) ∧
  frame.locals[15]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (input : ByteArray) (row index : Nat) (frame : Locals)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (row + 1) * 768 * 4 ≤ input.size)
    (hindex : index < 768)
    (hready : RangeFoldLoop.Ready 16 17 768 index frame)
    (hacc : Accumulator ptr input row index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 16 17 768 (index + 1) result →
      Accumulator ptr input row (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[13]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[14]? = some (.i64 768) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hrow64 : row < UInt64.size := by
    have := hbytes.1
    change row < 18446744073709551616
    omega
  have hbase64 : row * 768 < UInt64.size := by
    have := hbytes.1
    change row * 768 < 18446744073709551616
    omega
  have hoffset64 : row * 768 + index < UInt64.size := by
    have := hbytes.1
    change row * 768 + index < 18446744073709551616
    omega
  have hsafe : ¬ (-1 : UInt64) / 768 < UInt64.ofNat row := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hrow64]
    change ¬ 24019198012642645 < row
    have := hbytes.1
    omega
  have hmul : UInt64.ofNat row * 768 = UInt64.ofNat (row * 768) := by simp
  have hadd : UInt64.ofNat row * 768 + UInt64.ofNat index =
      UInt64.ofNat (row * 768 + index) := by simp
  have hsafeAdd : ¬ UInt64.ofNat row * 768 + UInt64.ofNat index < UInt64.ofNat row * 768 := by
    rw [hadd, hmul, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' hoffset64, UInt64.toNat_ofNat_of_lt' hbase64]
    omega
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hsafeInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by
    rw [hinc, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' (by change index + 1 < 18446744073709551616; omega),
      UInt64.toNat_ofNat_of_lt' (by change index < 18446744073709551616; omega)]
    omega
  simp only [stepCode, func1, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.dropLast,
    List.cons_append, List.nil_append]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafe)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafeAdd)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  simp only [hadd]
  refine wp_call_tw ((PackedWordRead.exact «module» 0 (some 0) rfl rfl
    env initial 0 ptr input (row * 768 + index) hbytes (by omega)).append_args
    rfl rfl rfl [.f32 (sumPrefix input row index)]) ?_
  rintro final values ⟨out, rfl, rfl, rfl⟩
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafeInc)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hparams, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc,
      true_and, and_self]
    rfl
  · simp only [Accumulator, hparams, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, sumPrefix_succ,
      LeanExe.Models.Gpt2.word, true_and, and_self]

#print axioms step_spec

end Project.Gpt2RowMean
