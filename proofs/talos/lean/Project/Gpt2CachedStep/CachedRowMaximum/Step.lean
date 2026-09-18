import Project.Gpt2CachedStep.Program
import Project.Gpt2CachedStep.CachedRowMaximum.Source
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.PackedWordRead
import Project.ProofKit.RangeFoldLoop
import Project.Gpt2CachedStep.FiniteLt
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.CachedRowMaximum

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func25[33]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

set_option maxRecDepth 16384 in
theorem emitted_loop :
    func25 = func25.take 33 ++ RangeFoldLoop.program 36 37 stepCode ++ func25.drop 34 := rfl

def Accumulator (owner ptr : UInt64) (input : ByteArray) (head size index : Nat) (frame : Locals) : Prop :=
  frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat head), .i64 (UInt64.ofNat size)] ∧
  frame.locals.length = 42 ∧
  frame.locals[6]? = some (.i64 (maximumPrefix input head size index).toUInt64) ∧
  frame.locals[33]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (head size index : Nat) (frame : Locals)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (head + 1) * size * 4 ≤ input.size) (hSize : 0 < size)
    (hindex : index < size)
    (hready : RangeFoldLoop.Ready 36 37 size index frame)
    (hacc : Accumulator owner ptr input head size index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 36 37 size (index + 1) result →
      Accumulator owner ptr input head size (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[31]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[32]? = some (.i64 (UInt64.ofNat size)) := by
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
  have hread := PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial owner ptr input (head * size + index) hbytes (by omega)
  have hcompare := FiniteLt.finiteLt_exact env initial
    (maximumPrefix input head size index) (word input (head * size + index))
  cases hlt : finiteLt (maximumPrefix input head size index) (word input (head * size + index)) <;>
    simp only [hlt, Bool.false_eq_true, reduceIte] at hcompare
  all_goals
    simp only [stepCode, func25, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.dropLast,
      List.cons_append, List.nil_append]
    repeat' first
      | wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1, hNonzero]
      | (refine wp_iff_cons rfl ?_
         first
         | rw [ite_eq_left (by decide)]
         | rw [ite_eq_right (by decide)]
         | rw [ite_eq_right (by simpa using hNonzero)]
         | rw [ite_eq_right (by simpa using hsafe)]
         | rw [ite_eq_right (by simpa using hsafeAdd)]
         | rw [ite_eq_right (by simpa using hsafeInc)])
      | (simp only [hadd]
         refine wp_call_tw hread ?_
         rintro final values ⟨rfl, rfl⟩)
      | (refine wp_call_tw hcompare ?_
         rintro final values ⟨rfl, rfl⟩)
    apply hnext
    · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc, true_and]
    · simp only [Accumulator, hlength, List.length_set, List.getElem?_set,
        Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, maximumPrefix_succ,
        hlt, Bool.false_eq_true, and_self] <;> simp only [word, and_self]

#print axioms step_spec

end Project.Gpt2CachedStep.CachedRowMaximum
