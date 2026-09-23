import Project.Gpt2QuantizedLinearRows.Program
import Project.Gpt2QuantizedLinearRows.RowScaleSource
import Project.ProofKit.PackedWordRead
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2QuantizedLinearRows.RowScale
open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func1[12]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

theorem emitted_loop :
    func1 = func1.take 12 ++ RangeFoldLoop.program 24 25 stepCode ++ func1.drop 13 := rfl

def Accumulator (owner ptr : UInt64) (input : ByteArray) (offset width index : Nat)
    (frame : Locals) : Prop :=
  frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size),
    .i64 (UInt64.ofNat offset), .i64 (UInt64.ofNat width)] ∧
  frame.locals.length = 28 ∧
  frame.locals[1]? = some (.i64 (maximumPrefix input offset index).toUInt64) ∧
  frame.locals[21]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (offset width index : Nat) (frame : Locals)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hsize : (offset + width) * 4 ≤ input.size) (hindex : index < width)
    (hready : RangeFoldLoop.Ready 24 25 width index frame)
    (hacc : Accumulator owner ptr input offset width index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 24 25 width (index + 1) result →
      Accumulator owner ptr input offset width (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[19]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[20]? = some (.i64 (UInt64.ofNat width)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hfit := hbytes.1
  have hadd := CheckedNatAdd.guard_of_fits offset index
    (by change offset + index < 18446744073709551616; omega)
  have hinc := CheckedNatAdd.guard_of_fits index 1
    (by change index + 1 < 18446744073709551616; omega)
  have hm : (2147483647 : UInt64) = (2147483647 : UInt32).toUInt64 := rfl
  simp only [stepCode, func1, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hadd)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  simp only [← UInt64.ofNat_add]
  refine wp_call_tw ((PackedWordRead.exact «module» 0 (some 0) rfl rfl
    env initial owner ptr input (offset + index) hbytes (by omega)).append_args
    rfl rfl rfl []) ?_
  rintro final values ⟨out, rfl, hfinal, rfl⟩
  subst final
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1,
    hm, widen_and, widen_lt]
  by_cases hcmp : maximumPrefix input offset index < (word input (offset + index) &&& 0x7FFFFFFF)
  all_goals
    simp only [word] at hcmp
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by simpa [word] using hcmp)]
          | rw [ite_eq_right (by simpa [word] using hcmp)]
    wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hadd)]
    wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    simp only [← UInt64.ofNat_add]
    refine wp_call_tw ((PackedWordRead.exact «module» 0 (some 0) rfl rfl
      env initial owner ptr input (offset + index) hbytes (by omega)).append_args
      rfl rfl rfl [.i64 (maximumPrefix input offset index).toUInt64]) ?_
    rintro final values ⟨out, rfl, hfinal, rfl⟩
    subst final
    wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1,
      hm, widen_and, widen_lt]
    refine wp_iff_cons rfl ?_
    first | rw [ite_eq_left (by simpa [word] using hcmp)]
          | rw [ite_eq_right (by simpa [word] using hcmp)]
    wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    refine wp_iff_cons rfl ?_
    rw [ite_eq_right (by simpa using hinc)]
    wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    apply hnext
    · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
        List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
        reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, UInt64.ofNat_add,
        true_and]
      exact ⟨rfl, trivial⟩
    · simp only [Accumulator, hlength, List.length_set, List.getElem?_set,
        Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, maximumPrefix_succ, hcmp,
        LeanExe.Models.Gpt2.word, and_self]

#print axioms step_spec

end Project.Gpt2QuantizedLinearRows.RowScale
