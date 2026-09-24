import Project.Gpt2CachedStep.FrozenProgram
import Project.Gpt2CachedStep.CachedRowSum.FrozenSource
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.PackedWordRead
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.Frozen.CachedRowSum

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func28[12]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

theorem emitted_loop :
    func28 = func28.take 12 ++ RangeFoldLoop.program 18 19 stepCode ++ func28.drop 13 := rfl

def Accumulator (owner ptr : UInt64) (input : ByteArray) (head size index : Nat) (frame : Locals) : Prop :=
  frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat head), .i64 (UInt64.ofNat size)] ∧
  frame.locals.length = 24 ∧
  frame.locals[1]? = some (.i64 (sumPrefix input head size index).toUInt64) ∧
  frame.locals[15]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (head size index : Nat) (frame : Locals)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (head + 1) * size * 4 ≤ input.size) (hSize : 0 < size)
    (hindex : index < size)
    (hready : RangeFoldLoop.Ready 18 19 size index frame)
    (hacc : Accumulator owner ptr input head size index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 18 19 size (index + 1) result →
      Accumulator owner ptr input head size (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[13]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[14]? = some (.i64 (UInt64.ofNat size)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hEnd : (head * size + size) * 4 ≤ input.size := by simpa [Nat.add_mul] using hrow
  have hProduct64 : head * size < UInt64.size := by
    have := hbytes.1
    change head * size < 18446744073709551616
    omega
  have hSize64 : size < UInt64.size := by
    have := hbytes.1
    change size < 18446744073709551616
    omega
  have hNonzero : UInt64.ofNat size ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_ofNat_of_lt' hSize64] at this
    change size = 0 at this
    omega
  have hsafe := CheckedNatMul.guard_of_nat_fits head size hProduct64 hNonzero
  have hadd : UInt64.ofNat head * UInt64.ofNat size + UInt64.ofNat index =
      UInt64.ofNat (head * size + index) := by simp
  have hsafeAdd : ¬ UInt64.ofNat head * UInt64.ofNat size + UInt64.ofNat index <
      UInt64.ofNat head * UInt64.ofNat size := by
    simpa only [UInt64.ofNat_mul] using CheckedNatAdd.guard_of_fits (head * size) index
      (by have := hbytes.1; change head * size + index < 18446744073709551616; omega)
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hsafeInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by
    rw [hinc, UInt64.lt_iff_toNat_lt,
      UInt64.toNat_ofNat_of_lt' (by have := hbytes.1; change index + 1 < 18446744073709551616; omega),
      UInt64.toNat_ofNat_of_lt' (by have := hbytes.1; change index < 18446744073709551616; omega)]
    omega
  simp only [stepCode, func28, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.dropLast,
    List.cons_append, List.nil_append]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hNonzero)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafe)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafeAdd)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
  simp only [hadd]
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial owner ptr input (head * size + index) hbytes (by omega)).append_args
    rfl rfl rfl [.f32 (sumPrefix input head size index)]) ?_
  rintro final values ⟨out, rfl, rfl, rfl⟩
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafeInc)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc,
      true_and]
  · simp only [Accumulator, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, sumPrefix_succ,
      LeanExe.Models.Gpt2.word, and_self]

#print axioms step_spec

end Project.Gpt2CachedStep.Frozen.CachedRowSum
