import Project.ClobDepth.FoundCopyInvariant
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Found-price level copy

The found branch copies every old level word into the fresh same-length
stride-two array.  The loop theorem applies the semantic transition from
`FoundCopyInvariant` at each iteration.
-/

namespace Project.ClobDepth.FoundCopy

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.FoundCopyInvariant

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_found_copy" "(" hParams:term "," hLocals:term ","
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
theorem foundCopyProg_spec
    (env : HostEnv Unit) (st0 : Store Unit) (base : Locals)
    (target source capacity : UInt64) (levels : List LevelL)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hSource : base.locals[10]? = some (.i64 source))
    (hTotal : base.locals[13]? =
      some (.i64 (UInt64.ofNat levels.length * 2)))
    (hTarget : base.locals[14]? = some (.i64 target))
    (hTotalU : (UInt64.ofNat levels.length * 2).toNat =
      levels.length * 2)
    (hTotal64 : levels.length * 2 < UInt64.size)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (levels.length * 2 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + (levels.length * 2 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target (levels.length * 2))
      (flatWordsRegion source (levels.length * 2)))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hInit : CopyInvariant st0 base target source capacity levels st0 base)
    (hDone : ∀ st1,
      CopyInvariant st0 base target source capacity levels st1
        (MissingCopyInvariant.copyLoopFrame base (levels.length * 2)) →
      wp «module» rest Q st1
        (MissingCopyInvariant.copyLoopFrame base (levels.length * 2)) env) :
    wp «module» (Entry.foundCopyProg ++ rest) Q st0 base env := by
  have hSource' : base.locals[10] = .i64 source := getElem_of_some hSource
  have hTotal' : base.locals[13] =
      .i64 (UInt64.ofNat levels.length * 2) := getElem_of_some hTotal
  have hTarget' : base.locals[14] = .i64 target := getElem_of_some hTarget
  simp only [Entry.foundCopyProg, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := CopyInvariant st0 base target source capacity levels)
    (μ := MissingCopyInvariant.copyMeasure (levels.length * 2))
  · exact hInit
  · rintro st1 s1 ⟨word, hWord, rfl, hState⟩
    have hWordU : (UInt64.ofNat word).toNat = word :=
      toNat_ofNat_lt (by omega)
    simp only [Entry.foundCopyBodyProg,
      MissingCopyInvariant.copyLoopFrame]
    wp_run_found_copy
      (hParams, hLocals, hValues, hSource', hTotal', hTarget')
    by_cases hEnd : word = levels.length * 2
    · have hge : UInt64.ofNat word ≥
          UInt64.ofNat levels.length * 2 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hWordU, hTotalU]
        omega
      rw [if_pos hge]
      try simp
      subst word
      apply hDone
      exact ⟨levels.length * 2, le_rfl, rfl, hState⟩
    · have hnge : ¬UInt64.ofNat word ≥
          UInt64.ofNat levels.length * 2 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hWordU, hTotalU]
        omega
      rw [if_neg hnge]
      try simp
      have hWordLt : word < levels.length * 2 :=
        Nat.lt_of_le_of_ne hWord hEnd
      have hSourceBound := hState.sourceCurrent.levelWord_bound_flat
        word hWordLt
      have hTargetLt : target.toNat + (word + 1) * 8 < 4294967296 := by
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
        · simp only [MissingCopyInvariant.copyLoopFrame, hWordNext]
        · simpa only [LevelCopyInvariant.copyWriteStore] using
            hState.advance hWordLt hTarget48 hSource32 hTarget32 hsep
      · simp [MissingCopyInvariant.copyMeasure, hLocals, hWordU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobDepth.FoundCopy
