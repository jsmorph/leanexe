import Project.Gpt2RowMean.Step

namespace Project.Gpt2RowMean.Spec

open Wasm Project.ProofKit PackedMemory LeanExe.Models.Gpt2

theorem rowMean_exact (env : HostEnv Unit) (initial : Store Unit)
    (ptr : UInt64) (input : ByteArray) (row : Nat)
    (hbytes : ByteArrayAt initial.mem ptr.toNat input)
    (hrow : (row + 1) * 768 * 4 ≤ input.size) :
    TerminatesWith env «module» 1 initial
      [.i64 (UInt64.ofNat row), .i64 (UInt64.ofNat input.size), .i64 ptr]
      (fun final values => final = initial ∧
        values = [.i64 (LeanExe.Models.Gpt2.rowMean input row).toUInt64]) := by
  have hcast (word : UInt32) : UInt32.ofNat (word.toUInt64.toNat % 2^32) = word := by simp
  have hmask (word : UInt32) : word.toUInt64 &&& 4294967295 = word.toUInt64 := by
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_and, UInt32.toNat_toUInt64]
    change word.toNat &&& (2^32 - 1) = word.toNat
    exact Nat.and_two_pow_sub_one_of_lt_two_pow word.toNat_lt
  refine TerminatesWith.of_wp_entry_for (f := func1Def) rfl ?_
  change wp «module» func1 _ initial
    { params := [.i64 ptr, .i64 (UInt64.ofNat input.size), .i64 (UInt64.ofNat row)],
      locals := List.replicate 24 (.i64 0), values := [] } env
  rw [emitted_loop, List.append_assoc]
  simp only [func1, List.take, List.drop, List.cons_append, List.nil_append]
  wp_run [Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  apply RangeFoldLoop.program_spec (count := 768) (P := Accumulator ptr input row)
  · decide
  · simp [RangeFoldLoop.Ready, Locals.get]
  · simp [Accumulator]
  · intro index next hindex hready hacc Q rest hnext
    exact step_spec env initial ptr input row index next hbytes hrow
      hindex hready hacc Q rest hnext
  · intro result hready hacc
    rcases hacc with ⟨hparams, hlength, htotal, hstride⟩
    wp_run [hparams, hlength, htotal, hready.1, Nat.reduceAdd, Nat.reduceLT,
      Nat.reduceSub, reduceIte, List.length_set, List.getElem?_set, Nat.reduceEqDiff,
      hcast, hmask, Wasm.f32Div]
    simp [func1Def, rowMean_eq, hmask]

#print axioms rowMean_exact

end Project.Gpt2RowMean.Spec
