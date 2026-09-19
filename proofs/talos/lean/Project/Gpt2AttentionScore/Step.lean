import Project.Gpt2AttentionScore.Program
import Project.Gpt2AttentionScore.Source
import Project.ProofKit.PackedWordRead
import Project.ProofKit.CheckedNatAddArithmetic
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2AttentionScore

open Wasm Project.Common Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func1[12]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

set_option maxRecDepth 16384 in
theorem emitted_loop :
    func1 = func1.take 12 ++ RangeFoldLoop.program 26 27 stepCode ++ func1.drop 13 := rfl

def Accumulator (ptr : UInt64) (input : ByteArray) (target source head index : Nat)
    (frame : Locals) : Prop :=
  frame.params = [.i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat target),
    .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat head)] ∧
  frame.locals.length = 38 ∧
  frame.locals[1]? = some (.i64 (dotPrefix input target source head index).toUInt64) ∧
  frame.locals[23]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (input : ByteArray) (target source head index : Nat) (frame : Locals)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (htarget : (target + 1) * 2304 * 4 ≤ input.size)
    (hsource : (source + 1) * 2304 * 4 ≤ input.size) (hhead : head < 12)
    (hindex : index < 64)
    (hready : RangeFoldLoop.Ready 26 27 64 index frame)
    (hacc : Accumulator ptr input target source head index frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 26 27 64 (index + 1) result →
      Accumulator ptr input target source head (index + 1) result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[21]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[22]? = some (.i64 64) := by
    simpa [Locals.get, hparams, hlength] using hready.2.2
  have hsize := hbytes.1
  have hMulT : ¬ (-1 : UInt64) / 2304 < UInt64.ofNat target := by
    change ¬ (8006399337547548 : UInt64) < UInt64.ofNat target
    u64_omega
  have hMulS : ¬ (-1 : UInt64) / 2304 < UInt64.ofNat source := by
    change ¬ (8006399337547548 : UInt64) < UInt64.ofNat source
    u64_omega
  have hMulH : ¬ (-1 : UInt64) / 64 < UInt64.ofNat head := by
    change ¬ (288230376151711743 : UInt64) < UInt64.ofNat head
    u64_omega
  have hQT : ¬ UInt64.ofNat target * 2304 + UInt64.ofNat head * 64 < UInt64.ofNat target * 2304 := by
    simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, show UInt64.ofNat 2304 = 2304 from rfl,
      show UInt64.ofNat 768 = 768 from rfl, show UInt64.ofNat 64 = 64 from rfl] using
      CheckedNatAdd.guard_of_fits (target * 2304) (head * 64)
        (by change target * 2304 + (head * 64) < 18446744073709551616; omega)
  have hQI : ¬ UInt64.ofNat target * 2304 + UInt64.ofNat head * 64 + UInt64.ofNat index <
      UInt64.ofNat target * 2304 + UInt64.ofNat head * 64 := by
    simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, show UInt64.ofNat 2304 = 2304 from rfl,
      show UInt64.ofNat 768 = 768 from rfl, show UInt64.ofNat 64 = 64 from rfl] using
      CheckedNatAdd.guard_of_fits (target * 2304 + head * 64) (index)
        (by change target * 2304 + head * 64 + (index) < 18446744073709551616; omega)
  have hSK : ¬ UInt64.ofNat source * 2304 + 768 < UInt64.ofNat source * 2304 := by
    simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, show UInt64.ofNat 2304 = 2304 from rfl,
      show UInt64.ofNat 768 = 768 from rfl, show UInt64.ofNat 64 = 64 from rfl] using
      CheckedNatAdd.guard_of_fits (source * 2304) (768)
        (by change source * 2304 + (768) < 18446744073709551616; omega)
  have hSH : ¬ UInt64.ofNat source * 2304 + 768 + UInt64.ofNat head * 64 <
      UInt64.ofNat source * 2304 + 768 := by
    simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, show UInt64.ofNat 2304 = 2304 from rfl,
      show UInt64.ofNat 768 = 768 from rfl, show UInt64.ofNat 64 = 64 from rfl] using
      CheckedNatAdd.guard_of_fits (source * 2304 + 768) (head * 64)
        (by change source * 2304 + 768 + (head * 64) < 18446744073709551616; omega)
  have hSI : ¬ UInt64.ofNat source * 2304 + 768 + UInt64.ofNat head * 64 + UInt64.ofNat index <
      UInt64.ofNat source * 2304 + 768 + UInt64.ofNat head * 64 := by
    simpa only [UInt64.ofNat_add, UInt64.ofNat_mul, show UInt64.ofNat 2304 = 2304 from rfl,
      show UInt64.ofNat 768 = 768 from rfl, show UInt64.ofNat 64 = 64 from rfl] using
      CheckedNatAdd.guard_of_fits (source * 2304 + 768 + head * 64) (index)
        (by change source * 2304 + 768 + head * 64 + (index) < 18446744073709551616; omega)
  have hInc : ¬ UInt64.ofNat index + 1 < UInt64.ofNat index := by u64_omega
  have hinc : UInt64.ofNat index + 1 = UInt64.ofNat (index + 1) := by simp
  have hquery : UInt64.ofNat target * 2304 + UInt64.ofNat head * 64 + UInt64.ofNat index =
      UInt64.ofNat (target * 2304 + head * 64 + index) := by simp
  have hkey : UInt64.ofNat source * 2304 + 768 + UInt64.ofNat head * 64 + UInt64.ofNat index =
      UInt64.ofNat (source * 2304 + 768 + head * 64 + index) := by simp
  simp only [stepCode, func1, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.drop, List.dropLast, List.cons_append, List.nil_append]
  repeat' first
    | wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hMulT, hMulH, hQT, hQI])])
  simp only [hquery]
  refine wp_call_tw (PackedWordRead.exact «module» 0 (some 0) rfl rfl
    env initial 0 ptr input (target * 2304 + head * 64 + index) hbytes (by omega)) ?_
  rintro final values ⟨rfl, rfl⟩
  repeat' first
    | wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
    | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hMulS, hMulH, hSK, hSH, hSI])])
  simp only [hkey]
  refine wp_call_tw (PackedWordRead.exact «module» 0 (some 0) rfl rfl
    env final 0 ptr input (source * 2304 + 768 + head * 64 + index) hbytes (by omega)) ?_
  rintro final' values ⟨rfl, rfl⟩
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hInc)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc, true_and]
    rfl
  · simp only [Accumulator, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, dotPrefix_succ,
      LeanExe.Models.Gpt2.word, and_self]

#print axioms step_spec

end Project.Gpt2AttentionScore
