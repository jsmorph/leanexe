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
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobLimit.LimitResidualCopyInvariant

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_copy" "(" hParams:term "," hLocals:term ","
    hValues:term "," hSource:term "," hTotal:term ","
    hTarget:term ")" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    List.length_set, List.getElem?_set,
    Nat.reduceAdd, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceSub,
    ValueType.zero, List.headD, ($hParams), ($hLocals), ($hValues),
    ($hSource), ($hTotal), ($hTarget)])

set_option Elab.async false in
theorem residualCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (g0 capacity : UInt64)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data g0)
    (hTotalU : (UInt64.ofNat ctx.result.book.length * 5).toNat =
      ctx.result.book.length * 5)
    (hTotal64 : ctx.result.book.length * 5 < UInt64.size)
    (hTargetNat : (g0 + 48).toNat = g0.toNat + 48)
    (hTarget48 : 48 ≤ (g0 + 48).toNat)
    (hSource32 : data.book.toNat +
      (ctx.result.book.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : (g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 < 4294967296)
    (hTargetFit : (g0 + 48).toNat +
      ((ctx.result.book.length + 1) * 5 + 1) * 8 ≤
        st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion (g0 + 48) ((ctx.result.book.length + 1) * 5))
      (flatWordsRegion data.book (ctx.result.book.length * 5)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hInit : CopyInvariant st0 base (g0 + 48) data.book capacity
      ctx.result.book st0 base)
    (hDone : ∀ st1,
      CopyInvariant st0 base (g0 + 48) data.book capacity
        ctx.result.book st1
        (copyLoopFrame base (ctx.result.book.length * 5)) →
      wp «module» rest Q st1
        (copyLoopFrame base (ctx.result.book.length * 5)) env) :
    wp «module» (LimitEntry.residualCopyProg ++ rest) Q st0 base env := by
  have hParams := hCopy.orderLocals.fields.params
  have hLocals := hCopy.orderLocals.fields.locals
  have hValues := hCopy.orderLocals.fields.values
  have hSource : base.locals[34] = .i64 data.book := by
    apply Option.some.inj
    calc
      some base.locals[34] = base.locals[34]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 data.book) := hCopy.orderLocals.fields.source
  have hTotal : base.locals[36] =
      .i64 (UInt64.ofNat ctx.result.book.length * 5) := by
    apply Option.some.inj
    calc
      some base.locals[36] = base.locals[36]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (UInt64.ofNat ctx.result.book.length * 5)) :=
        hCopy.orderLocals.total
  have hTarget : base.locals[38] = .i64 (g0 + 48) := by
    apply Option.some.inj
    calc
      some base.locals[38] = base.locals[38]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 (g0 + 48)) := hCopy.target
  simp only [LimitEntry.residualCopyProg, List.cons_append,
    List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := CopyInvariant st0 base (g0 + 48) data.book capacity
      ctx.result.book)
    (μ := copyMeasure (ctx.result.book.length * 5))
  · exact hInit
  · rintro st1 s1 ⟨word, hWord, rfl, hState⟩
    have hWordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [LimitEntry.residualCopyBodyProg, copyLoopFrame]
    wp_run_copy (hParams, hLocals, hValues, hSource, hTotal, hTarget)
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
      have hTargetLt : (g0 + 48).toNat + (word + 1) * 8 <
          4294967296 := by
        omega
      have hTargetBound :
          (g0.toNat + 48 + (word + 1) * 8) % 4294967296 + 8 ≤
            st1.mem.pages * 65536 := by
        rw [← hTargetNat, Nat.mod_eq_of_lt hTargetLt, hState.pages]
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
        · simpa only [copyWriteStore, hTargetNat] using
            hState.advance hWordLt hTarget48 hSource32 hTarget32 hsep
      · simp [copyMeasure, hLocals, hWordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobLimit.LimitResidualCopy
