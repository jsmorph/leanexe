import Project.Gpt2CachedStep.Program
import Project.Gpt2RowInvStd.Source
import Project.ProofKit.PackedWordRead
import Project.ProofKit.RangeFoldLoop
import Project.ProofKit.PackedFloatFrame

namespace Project.Gpt2CachedStep.RowInvStd

open Project.Gpt2RowInvStd (variancePrefix variancePrefix_succ rowInvStd_eq)

open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

def stepCode : Wasm.Program :=
  match (func19[12]? : Option Wasm.Instruction) with
  | some (Wasm.Instruction.block _ _ [Wasm.Instruction.loop _ _ body _ _] _ _) => (body.drop 4).dropLast
  | _ => []

theorem emitted_loop :
    func19 = func19.take 12 ++ RangeFoldLoop.program 21 22 stepCode ++ func19.drop 13 := rfl

def Accumulator (owner ptr : UInt64) (input : ByteArray) (row index : Nat) (mean : UInt32) (frame : Locals) : Prop :=
  frame.params = [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat row), .i64 mean.toUInt64] ∧
  frame.locals.length = 27 ∧
  frame.locals[1]? = some (.i64 (variancePrefix input row mean index).toUInt64) ∧
  frame.locals[18]? = some (.i64 1)

set_option maxRecDepth 16384 in
theorem step_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (row index : Nat) (mean : UInt32) (frame : Locals)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (row + 1) * 768 * 4 ≤ input.size)
    (hindex : index < 768)
    (hready : RangeFoldLoop.Ready 21 22 768 index frame)
    (hacc : Accumulator owner ptr input row index mean frame)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : ∀ result, RangeFoldLoop.Ready 21 22 768 (index + 1) result →
      Accumulator owner ptr input row (index + 1) mean result → wp «module» rest Q initial result env) :
    wp «module» (stepCode ++ rest) Q initial frame env := by
  rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
  have hcounter : frame.locals[16]? = some (.i64 (UInt64.ofNat index)) := by
    simpa [Locals.get, hparams, hlength] using hready.2.1
  have hstop : frame.locals[17]? = some (.i64 768) := by
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
  simp only [stepCode, func19, List.getElem?_cons_zero, List.getElem?_cons_succ, List.drop, List.dropLast,
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
  refine wp_call_tw ((PackedWordRead.exact «module» 17 (some 17) rfl rfl
    env initial owner ptr input (row * 768 + index) hbytes (by omega)).append_args
    rfl rfl rfl []) ?_
  rintro final values ⟨out, rfl, rfl, rfl⟩
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hsafeInc)]
  wp_packed_frame [hparams, hlength, htotal, hcounter, hstop, hstride, hready.1]
  apply hnext
  · simp only [RangeFoldLoop.Ready, Locals.get, hlength, List.length_set,
      List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub,
      reduceIte, List.getElem?_set, Nat.reduceEqDiff, hstop, hinc,
      true_and]
    rfl
  · simp only [Accumulator, hlength, List.length_set, List.getElem?_set,
      Nat.reduceLT, Nat.reduceEqDiff, reduceIte, hstride, variancePrefix_succ,
      LeanExe.Models.Gpt2.word, and_self]

theorem rowInvStd_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (row : Nat) (mean : UInt32)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (row + 1) * 768 * 4 ≤ input.size) :
    TerminatesWith env «module» 19 initial
      [.i64 mean.toUInt64, .i64 (UInt64.ofNat row), .i64 (UInt64.ofNat input.size), .i64 ptr, .i64 owner]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.rowInvStd input row mean).toUInt64]) := by
  refine TerminatesWith.of_wp_entry_for (f := func19Def) rfl ?_
  change wp «module» func19 _ initial
    { params := [.i64 owner, .i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat row), .i64 mean.toUInt64],
      locals := List.replicate 27 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func19, List.take, List.drop, List.cons_append, List.nil_append]
  wp_packed_frame
  apply RangeFoldLoop.program_spec (count := 768) (P := fun index => Accumulator owner ptr input row index mean)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial owner ptr input row index mean next hbytes hrow
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_packed_frame [hparams, hlength, htotal, hready.1]
    simp [func19Def, rowInvStd_eq]

#print axioms rowInvStd_exact

end Project.Gpt2CachedStep.RowInvStd
