import Project.ClobDepth.Representation

/-!
# Shared level-copy invariant

This invariant covers stride-two copies into append-sized and same-length
targets.  Generated cursor locals and loop instructions remain in their branch
modules.
-/

namespace Project.ClobDepth.LevelCopyInvariant

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation

structure CopyState (st0 st : Store Unit) (target source capacity : UInt64)
    (levels : List LevelL) (targetLength targetWords word : Nat) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  fresh : FreshFixedArrayAt st target capacity 2
  length : st.mem.read64 target.toUInt32 = UInt64.ofNat targetLength
  sourceInitial : LevelsAt st0 source levels
  sourceCurrent : LevelsAt st source levels
  outside : MemEqOutsideFlatWords st0 st target targetWords
  copied : ∀ copied : Nat, copied < word →
    levelWord st target copied = levelWord st0 source copied

def copyWriteStore (st : Store Unit) (target source : UInt64)
    (word : Nat) : Store Unit :=
  { st with
    mem := st.mem.write64
      (UInt32.ofNat ((target.toNat + (word + 1) * 8) % 4294967296))
      (st.mem.read64
        (UInt32.ofNat ((source.toNat + (word + 1) * 8) % 4294967296))) }

theorem CopyState.initial
    {st : Store Unit} {target source capacity : UInt64}
    {levels : List LevelL} {targetLength targetWords : Nat}
    (hFresh : FreshFixedArrayAt st target capacity 2)
    (hLength : st.mem.read64 target.toUInt32 = UInt64.ofNat targetLength)
    (hSource : LevelsAt st source levels) :
    CopyState st st target source capacity levels targetLength targetWords 0 := by
  exact {
    pages := rfl
    globals := rfl
    fresh := hFresh
    length := hLength
    sourceInitial := hSource
    sourceCurrent := hSource
    outside := by intro _ _; rfl
    copied := by intro _ h; omega }

theorem CopyState.advance
    {st0 st : Store Unit} {target source capacity : UInt64}
    {levels : List LevelL} {targetLength targetWords word : Nat}
    (hState : CopyState st0 st target source capacity levels targetLength
      targetWords word)
    (hWord : word < levels.length * 2)
    (hSourceFits : levels.length * 2 ≤ targetWords)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (targetWords + 1) * 8 < 4294967296)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target targetWords)
      (flatWordsRegion source (levels.length * 2))) :
    CopyState st0 (copyWriteStore st target source word) target source
      capacity levels targetLength targetWords (word + 1) := by
  have hTargetLt : target.toNat + (word + 1) * 8 < 4294967296 := by
    omega
  refine {
    pages := by simp [copyWriteStore, hState.pages]
    globals := hState.globals
    fresh := ?_
    length := ?_
    sourceInitial := hState.sourceInitial
    sourceCurrent := ?_
    outside := ?_
    copied := ?_ }
  · refine FreshFixedArrayAt.write64_data hState.fresh hTarget48 ?_
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt hTargetLt]
    omega
  · simp only [copyWriteStore]
    rw [read64_write64_ne _ _ _ _ (by
      simp only [toUInt32_eq_ofNat, toUInt32_ofNat_mod_toNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hTargetLt]
      omega)]
    exact hState.length
  · simpa only [copyWriteStore] using
      hState.sourceCurrent.frame_write64_flatWordsDisjoint hSource32
        hTarget32 (slot := word + 1)
        (value := st.mem.read64 (UInt32.ofNat
          ((source.toNat + (word + 1) * 8) % 4294967296)))
        (by omega) hsep
  · exact hState.outside.write64 hTarget32 (by omega)
  · intro copied hCopied
    unfold levelWord
    by_cases hCurrent : copied = word
    · subst copied
      simp only [copyWriteStore]
      rw [Mem.read64_write64_same]
      have hSourceCurrent := hState.sourceCurrent.levelWord_eq_flat word hWord
      have hSourceInitial := hState.sourceInitial.levelWord_eq_flat word hWord
      unfold levelWord at hSourceCurrent hSourceInitial
      exact hSourceCurrent.trans hSourceInitial.symm
    · simp only [copyWriteStore]
      rw [read64_write64_ne _ _ _ _ (by
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hTargetLt]
        omega)]
      have hPrevious := hState.copied copied (by omega)
      unfold levelWord at hPrevious
      exact hPrevious

end Project.ClobDepth.LevelCopyInvariant
