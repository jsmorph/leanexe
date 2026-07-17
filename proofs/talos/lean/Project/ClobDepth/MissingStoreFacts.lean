import Project.ClobDepth.MissingCopy

/-!
# Missing-price final-store facts

The final two stores append one level after the copied flat-word prefix.  The
semantic theorem reconstructs the represented extended level list and retains
the allocator and memory-frame facts needed by branch composition.
-/

namespace Project.ClobDepth.MissingStoreFacts

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.MissingCopyInvariant

def appendLevelStore (st : Store Unit) (target : UInt64) (n : Nat)
    (level : LevelL) : Store Unit :=
  { st with
    mem := (st.mem.write64
      (UInt32.ofNat
        ((target.toNat + (n * 2 + 1) * 8) % 4294967296))
      level.lprice).write64
      (UInt32.ofNat
        ((target.toNat + (n * 2 + 2) * 8) % 4294967296))
      level.lqty }

theorem appendLevelStore_read_before
    (st : Store Unit) (target : UInt64) (n : Nat) (level : LevelL)
    (b : UInt32)
    (hAddr : target.toNat + (n * 2 + 2) * 8 < 4294967296)
    (hBefore : b.toNat + 8 ≤ target.toNat + (n * 2 + 1) * 8) :
    (appendLevelStore st target n level).mem.read64 b =
      st.mem.read64 b := by
  unfold appendLevelStore
  rw [read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl (hBefore.trans (by omega))),
    read64_write64_ne _ _ _ _ (by
        rw [toUInt32_ofNat_mod_toNat,
          Nat.mod_eq_of_lt (by omega)]
        exact Or.inl hBefore)]

theorem appendLevelStore_reads
    (st : Store Unit) (target : UInt64) (n : Nat) (level : LevelL)
    (hAddr : target.toNat + (n * 2 + 2) * 8 < 4294967296) :
    (appendLevelStore st target n level).mem.read64
        (UInt32.ofNat
          ((target.toNat + (n * 2 + 1) * 8) % 4294967296)) =
          level.lprice ∧
    (appendLevelStore st target n level).mem.read64
        (UInt32.ofNat
          ((target.toNat + (n * 2 + 2) * 8) % 4294967296)) =
          level.lqty := by
  have hAddress (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      (UInt32.ofNat
        ((target.toNat + (n * 2 + field) * 8) % 4294967296)).toNat =
        target.toNat + (n * 2 + field) * 8 := by
    rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
  have hDisjoint :
      (UInt32.ofNat
        ((target.toNat + (n * 2 + 1) * 8) % 4294967296)).toNat + 8 ≤
        (UInt32.ofNat
          ((target.toNat + (n * 2 + 2) * 8) % 4294967296)).toNat := by
    rw [hAddress 1 (by omega) (by omega),
      hAddress 2 (by omega) (by omega)]
    omega
  unfold appendLevelStore
  constructor
  · rw [read64_write64_ne _ _ _ _ (Or.inl hDisjoint),
      Mem.read64_write64_same]
  · rw [Mem.read64_write64_same]

structure FinishState (st0 st : Store Unit)
    (target source capacity : UInt64) (levels : List LevelL)
    (level : LevelL) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  levelsOwned : OwnedLevelArrayAt st target capacity (levels ++ [level])
  sourceCurrent : LevelsAt st source levels
  outside : MemEqOutsideFlatWords st0 st target ((levels.length + 1) * 2)

theorem finish
    {st0 st1 : Store Unit} {target source capacity : UInt64}
    {levels : List LevelL} {level : LevelL}
    (hState : CopyState st0 st1 target source capacity levels
      (levels.length * 2))
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + ((levels.length + 1) * 2 + 1) * 8 <
      4294967296)
    (hTargetFit : target.toNat + ((levels.length + 1) * 2 + 1) * 8 ≤
      st0.mem.pages * 65536)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((levels.length + 1) * 2))
      (flatWordsRegion source (levels.length * 2))) :
    FinishState st0 (appendLevelStore st1 target levels.length level)
      target source capacity levels level := by
  have hAddr (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      target.toNat + (levels.length * 2 + field) * 8 < 4294967296 := by
    omega
  have hData (field : Nat) (hField1 : 1 ≤ field)
      (hField2 : field ≤ 2) :
      target.toNat ≤
        (UInt32.ofNat
          ((target.toNat + (levels.length * 2 + field) * 8) %
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
      hTarget32 (slot := levels.length * 2 + 1) (value := level.lprice)
      (by omega) hsep
  have hSource2 :=
    hSource1.frame_write64_flatWordsDisjoint hSource32 hTarget32
      (slot := levels.length * 2 + 2) (value := level.lqty)
      (by omega) hsep
  have hOutside1 := hState.outside.write64
    (value := level.lprice) hTarget32
    (slot := levels.length * 2 + 1) (by omega)
  have hOutside2 := hOutside1.write64
    (value := level.lqty) hTarget32
    (slot := levels.length * 2 + 2) (by omega)
  have hStoreAddr :
      target.toNat + (levels.length * 2 + 2) * 8 < 4294967296 :=
    hAddr 2 (by omega) (by omega)
  have hReads := appendLevelStore_reads st1 target levels.length level
    hStoreAddr
  have hLevels : LevelsAt
      (appendLevelStore st1 target levels.length level) target
      (levels ++ [level]) := by
    apply LevelsAt.ofFlatWords
    · have hRead := appendLevelStore_read_before st1 target levels.length
          level (UInt32.ofNat (target.toNat % 4294967296)) hStoreAddr
          (by
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega)]
            omega)
      calc
        _ = st1.mem.read64
            (UInt32.ofNat (target.toNat % 4294967296)) := hRead
        _ = UInt64.ofNat (levels.length + 1) := by
          rw [← toUInt32_eq_ofNat]
          exact hState.length
        _ = UInt64.ofNat (levels ++ [level]).length := by simp
    · simp only [appendLevelStore, Mem.write64_pages, hState.pages]
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    · intro j hj field hField
      by_cases hOld : j < levels.length
      · have hGet : (levels ++ [level])[j]! = levels[j]! := by
          rw [getBang_eq hj, getBang_eq hOld]
          exact List.getElem_append_left hOld
        rw [hGet]
        calc
          levelWord (appendLevelStore st1 target levels.length level) target
              (j * 2 + field) = levelWord st1 target (j * 2 + field) := by
            unfold levelWord
            apply appendLevelStore_read_before st1 target levels.length
              level _ hStoreAddr
            rw [toUInt32_ofNat_mod_toNat,
              Nat.mod_eq_of_lt (by omega)]
            omega
          _ = levelWord st0 source (j * 2 + field) :=
            hState.copied _ (by omega)
          _ = LevelL.word levels[j]! field :=
            hState.sourceInitial.levelWord_eq j field hOld hField
      · have hjEq : j = levels.length := by
          simp at hj
          omega
        subst j
        have hGet : (levels ++ [level])[levels.length]! = level := by
          simp [getElem!_pos]
        rw [hGet]
        obtain ⟨hPrice, hQty⟩ := hReads
        interval_cases field
        · unfold levelWord
          simpa only [LevelL.word] using hPrice
        · unfold levelWord
          simpa only [LevelL.word] using hQty
    · intro j hj field hField
      have hj' : j < levels.length + 1 := by simpa using hj
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

end Project.ClobDepth.MissingStoreFacts
