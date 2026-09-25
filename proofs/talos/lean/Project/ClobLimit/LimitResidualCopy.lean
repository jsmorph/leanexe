import Project.ClobLimit.LimitResidualCopyInvariant
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Residual book copy

The residual branch copies every word of the matched book into the fresh
stride-five array.  The loop theorem applies the separately compiled semantic
transition at each write.  The appended order stores remain in the following
proof boundary.
-/

namespace Project.ClobLimit.LimitResidualCopy

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.MatchInvariant
  Project.ClobLimit.LimitResidualCopyInvariant

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576


set_option Elab.async false in
theorem residualCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : MatchOutput.OutputData) (target capacity : UInt64)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data target)
    (hTotalU : (UInt64.ofNat ctx.result.book.length * 5).toNat =
      ctx.result.book.length * 5)
    (hTotal64 : ctx.result.book.length * 5 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : data.book.toNat +
      (ctx.result.book.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : target.toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
        st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((ctx.result.book.length + 1) * 5))
      (flatWordsRegion data.book (ctx.result.book.length * 5)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hInit : CopyInvariant st0 base target data.book capacity
      ctx.result.book st0 base)
    (hDone : ∀ st1,
      CopyInvariant st0 base target data.book capacity
        ctx.result.book st1
        (copyLoopFrame base (ctx.result.book.length * 5)) →
      wp «module» rest Q st1
        (copyLoopFrame base (ctx.result.book.length * 5)) env) :
    wp «module» (LimitEntry.residualCopyProg ++ rest) Q st0 base env := by
  have hParams := hCopy.orderLocals.fields.params
  have hLocals := hCopy.orderLocals.fields.locals
  have hValues := hCopy.orderLocals.fields.values
  have hSource : base.locals[36] = .i64 data.book := getElem_of_some hCopy.orderLocals.fields.source
  have hTotal : base.locals[38] =
      .i64 (UInt64.ofNat ctx.result.book.length * 5) := getElem_of_some hCopy.orderLocals.total
  have hTarget : base.locals[40] = .i64 target := getElem_of_some hCopy.target
  simp only [LimitEntry.residualCopyProg, List.cons_append,
    List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := CopyInvariant st0 base target data.book capacity
      ctx.result.book)
    (μ := copyMeasure (ctx.result.book.length * 5))
  · exact hInit
  · rintro st1 s1 ⟨word, hWord, rfl, hState⟩
    have hWordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [LimitEntry.residualCopyBodyProg, copyLoopFrame]
    wp_run_with [hParams, hLocals, hValues, hSource, hTotal, hTarget]
    by_cases hEnd : word = ctx.result.book.length * 5
    · have hge : UInt64.ofNat word ≥
          UInt64.ofNat ctx.result.book.length * 5 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hWordU, hTotalU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      exact ⟨ctx.result.book.length * 5, le_rfl, rfl, hState⟩
    · have hnge : ¬UInt64.ofNat word ≥
          UInt64.ofNat ctx.result.book.length * 5 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hWordU, hTotalU]
        omega
      rw [if_neg hnge]
      try simp
      have hWordLt : word < ctx.result.book.length * 5 :=
        Nat.lt_of_le_of_ne hWord hEnd
      have hSourceBound := hState.sourceCurrent.orderWord_bound_flat
        word hWordLt
      have hTargetLt : target.toNat + (word + 1) * 8 <
          4294967296 := by
        omega
      have hTargetBound :
          (target.toNat + (word + 1) * 8) % 4294967296 + 8 ≤
            st1.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt hTargetLt, hState.pages]
        omega
      rw [if_neg (Nat.not_lt.mpr hSourceBound),
        if_neg (Nat.not_lt.mpr hTargetBound)]
      refine ⟨?_, ?_⟩
      · have hWordNext : UInt64.ofNat word + 1 =
            UInt64.ofNat (word + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hWordU, size_eq]; omega), hWordU,
            toNat_ofNat_lt (by omega)]
        refine ⟨word + 1, by omega, ?_, ?_⟩
        · simp only [copyLoopFrame, hWordNext]
        · simpa only [copyWriteStore] using
            hState.advance hWordLt hTarget48 hSource32 hTarget32 hsep
      · simp [copyMeasure, hLocals, hWordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobLimit.LimitResidualCopy
