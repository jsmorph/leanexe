import Project.ClobDepth.FoundCopy
import Project.ClobDepth.MissingStoreFacts

/-!
# Found-price final-store facts

The final two stores overwrite the matched level inside the copied flat-word
region.  The semantic theorem reconstructs the represented list with the
replaced level and retains the allocator and memory-frame facts needed by
branch composition.  The store definition comes from the missing branch with
the matched index as its slot.
-/

namespace Project.ClobDepth.FoundStoreFacts

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.FoundCopyInvariant
  Project.ClobDepth.MissingStoreFacts

theorem replaceStore_read_other
    (st : Store Unit) (target : UInt64) (i : Nat) (level : LevelL)
    (w : Nat)
    (hAddr : target.toNat + (i * 2 + 2) * 8 < 4294967296)
    (hwAddr : target.toNat + (w + 1) * 8 < 4294967296)
    (hNe0 : w ≠ i * 2) (hNe1 : w ≠ i * 2 + 1) :
    (appendLevelStore st target i level).mem.read64
        (UInt32.ofNat ((target.toNat + (w + 1) * 8) % 4294967296)) =
      st.mem.read64
        (UInt32.ofNat ((target.toNat + (w + 1) * 8) % 4294967296)) := by
  unfold appendLevelStore
  rw [read64_write64_ne _ _ _ _ (by
      simp only [toUInt32_ofNat_mod_toNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega),
    read64_write64_ne _ _ _ _ (by
      simp only [toUInt32_ofNat_mod_toNat]
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
      omega)]

structure ReplaceState (st0 st : Store Unit)
    (target source capacity : UInt64) (levels : List LevelL)
    (i : Nat) (level : LevelL) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  levelsOwned : OwnedLevelArrayAt st target capacity (levels.set i level)
  sourceCurrent : LevelsAt st source levels
  outside : MemEqOutsideFlatWords st0 st target (levels.length * 2)

theorem finish
    {st0 st1 : Store Unit} {target source capacity : UInt64}
    {levels : List LevelL} {level : LevelL} {i : Nat}
    (hState : CopyState st0 st1 target source capacity levels
      (levels.length * 2))
    (hi : i < levels.length)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + (levels.length * 2 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + (levels.length * 2 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target (levels.length * 2))
      (flatWordsRegion source (levels.length * 2))) :
    ReplaceState st0 (appendLevelStore st1 target i level)
      target source capacity levels i level := by
  have hAddr (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      target.toNat + (i * 2 + field) * 8 < 4294967296 := by
    omega
  have hData (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      target.toNat ≤
        (UInt32.ofNat
          ((target.toNat + (i * 2 + field) * 8) %
            4294967296)).toNat := by
    rw [toUInt32_ofNat_mod_toNat,
      Nat.mod_eq_of_lt (hAddr field hField1 hField2)]
    omega
  have hFresh1 := FreshFixedArrayAt.write64_data
    (value := level.lprice) hState.fresh hTarget48
    (hData 1 (by omega) (by omega))
  have hFresh2 := FreshFixedArrayAt.write64_data
    (value := level.lqty) hFresh1 hTarget48
    (hData 2 (by omega) (by omega))
  have hSource1 :=
    hState.sourceCurrent.frame_write64_flatWordsDisjoint hSource32
      hTarget32 (slot := i * 2 + 1) (value := level.lprice)
      (by omega) hsep
  have hSource2 :=
    hSource1.frame_write64_flatWordsDisjoint hSource32 hTarget32
      (slot := i * 2 + 2) (value := level.lqty)
      (by omega) hsep
  have hOutside1 := hState.outside.write64
    (value := level.lprice) hTarget32
    (slot := i * 2 + 1) (by omega)
  have hOutside2 := hOutside1.write64
    (value := level.lqty) hTarget32
    (slot := i * 2 + 2) (by omega)
  have hStoreAddr :
      target.toNat + (i * 2 + 2) * 8 < 4294967296 :=
    hAddr 2 (by omega) (by omega)
  have hReads := appendLevelStore_reads st1 target i level hStoreAddr
  have hLevels : LevelsAt
      (appendLevelStore st1 target i level) target
      (levels.set i level) := by
    apply LevelsAt.ofFlatWords
    · have hRead := appendLevelStore_read_before st1 target i
          level (UInt32.ofNat (target.toNat % 4294967296)) hStoreAddr
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega)]
            omega)
      calc
        _ = st1.mem.read64
            (UInt32.ofNat (target.toNat % 4294967296)) := hRead
        _ = UInt64.ofNat levels.length := by
          rw [← toUInt32_eq_ofNat]
          exact hState.length
        _ = UInt64.ofNat (levels.set i level).length := by simp
    · simp only [appendLevelStore, Mem.write64_pages, hState.pages]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · intro j hj field hField
      have hj' : j < levels.length := by simpa using hj
      by_cases hOther : j = i
      · subst j
        have hGet : (levels.set i level)[i]! = level := by
          rw [getBang_eq (by simpa using hj)]
          exact List.getElem_set_self _
        rw [hGet]
        obtain ⟨hPrice, hQty⟩ := hReads
        interval_cases field
        · unfold levelWord
          simpa only [LevelL.word] using hPrice
        · unfold levelWord
          simpa only [LevelL.word] using hQty
      · have hGet : (levels.set i level)[j]! = levels[j]! := by
          rw [getBang_eq (by simpa using hj), getBang_eq hj']
          exact List.getElem_set_ne (Ne.symm hOther) _
        rw [hGet]
        calc
          levelWord (appendLevelStore st1 target i level) target
              (j * 2 + field) = levelWord st1 target (j * 2 + field) := by
            unfold levelWord
            exact replaceStore_read_other st1 target i level
              (j * 2 + field) hStoreAddr (by omega) (by omega) (by omega)
          _ = levelWord st0 source (j * 2 + field) :=
            hState.copied _ (by omega)
          _ = LevelL.word levels[j]! field :=
            hState.sourceInitial.levelWord_eq j field hj' hField
    · intro j hj field hField
      have hj' : j < levels.length := by simpa using hj
      simp only [appendLevelStore, Mem.write64_pages]
      rw [Nat.mod_eq_of_lt (by omega), hState.pages]
      omega
  refine {
    pages := by simp [appendLevelStore, hState.pages]
    globals := hState.globals
    levelsOwned := ⟨?_, hLevels⟩
    sourceCurrent := ?_
    outside := ?_ }
  · simpa only [appendLevelStore] using hFresh2
  · simpa only [appendLevelStore] using hSource2
  · simpa only [appendLevelStore] using hOutside2

end Project.ClobDepth.FoundStoreFacts
