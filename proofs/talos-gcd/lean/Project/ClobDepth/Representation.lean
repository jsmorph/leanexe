import Project.ClobDepth.Model

/-!
# Depth level-array representation

The depth artifact stores one level as two consecutive `UInt64` words.  This
module relates that layout to the source model and combines it with the shared
owned fixed-array header.
-/

namespace Project.ClobDepth.Representation

open Wasm Project.Clob Project.ClobDepth.Model

def LevelL.word (level : LevelL) (field : Nat) : UInt64 :=
  match field with
  | 0 => level.lprice
  | 1 => level.lqty
  | _ => 0

def levelWord (st : Store Unit) (ptr : UInt64) (word : Nat) : UInt64 :=
  st.mem.read64
    (UInt32.ofNat ((ptr.toNat + (word + 1) * 8) % 4294967296))

def LevelsAt (st : Store Unit) (ptr : UInt64) (levels : List LevelL) : Prop :=
  (st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) =
      UInt64.ofNat levels.length ∧
    ptr.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536) ∧
  ∀ j : Nat, j < levels.length →
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 2 + 1) * 8) % 4294967296)) =
          levels[j]!.lprice ∧
      (ptr.toNat + (j * 2 + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) ∧
    (st.mem.read64
        (UInt32.ofNat ((ptr.toNat + (j * 2 + 2) * 8) % 4294967296)) =
          levels[j]!.lqty ∧
      (ptr.toNat + (j * 2 + 2) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536)

def OwnedLevelArrayAt (st : Store Unit) (ptr capacity : UInt64)
    (levels : List LevelL) : Prop :=
  FreshFixedArrayAt st ptr capacity 2 ∧ LevelsAt st ptr levels

theorem LevelsAt.levelWord_eq {st : Store Unit} {ptr : UInt64}
    {levels : List LevelL} (hLevels : LevelsAt st ptr levels) (j field : Nat)
    (hj : j < levels.length) (hfield : field < 2) :
    levelWord st ptr (j * 2 + field) = LevelL.word levels[j]! field := by
  obtain ⟨h1, h2⟩ := hLevels.2 j hj
  unfold levelWord
  rw [show j * 2 + field + 1 = j * 2 + (field + 1) by omega]
  interval_cases field
  · simpa [LevelL.word] using h1.1
  · simpa [LevelL.word] using h2.1

theorem LevelsAt.levelWord_bound {st : Store Unit} {ptr : UInt64}
    {levels : List LevelL} (hLevels : LevelsAt st ptr levels) (j field : Nat)
    (hj : j < levels.length) (hfield : field < 2) :
    (ptr.toNat + (j * 2 + field + 1) * 8) % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
  obtain ⟨h1, h2⟩ := hLevels.2 j hj
  interval_cases field
  · simpa using h1.2
  · simpa using h2.2

theorem LevelsAt.levelWord_eq_flat {st : Store Unit} {ptr : UInt64}
    {levels : List LevelL} (hLevels : LevelsAt st ptr levels) (word : Nat)
    (hword : word < levels.length * 2) :
    levelWord st ptr word = LevelL.word levels[word / 2]! (word % 2) := by
  have hfield : word % 2 < 2 := Nat.mod_lt _ (by decide)
  have hindex : word / 2 < levels.length :=
    (Nat.div_lt_iff_lt_mul (by decide)).2 hword
  have h := hLevels.levelWord_eq (word / 2) (word % 2) hindex hfield
  simpa only [Nat.div_add_mod'] using h

theorem LevelsAt.levelWord_bound_flat {st : Store Unit} {ptr : UInt64}
    {levels : List LevelL} (hLevels : LevelsAt st ptr levels) (word : Nat)
    (hword : word < levels.length * 2) :
    (ptr.toNat + (word + 1) * 8) % 4294967296 + 8 ≤
      st.mem.pages * 65536 := by
  have hfield : word % 2 < 2 := Nat.mod_lt _ (by decide)
  have hindex : word / 2 < levels.length :=
    (Nat.div_lt_iff_lt_mul (by decide)).2 hword
  have h := hLevels.levelWord_bound (word / 2) (word % 2) hindex hfield
  simpa only [Nat.div_add_mod'] using h

theorem LevelsAt.ofFlatWords {st : Store Unit} {ptr : UInt64}
    {levels : List LevelL}
    (hLength : st.mem.read64 (UInt32.ofNat (ptr.toNat % 4294967296)) =
      UInt64.ofNat levels.length)
    (hLengthBound : ptr.toNat % 4294967296 + 8 ≤ st.mem.pages * 65536)
    (hWord : ∀ (j : Nat), j < levels.length → ∀ field : Nat, field < 2 →
      levelWord st ptr (j * 2 + field) = LevelL.word levels[j]! field)
    (hBound : ∀ (j : Nat), j < levels.length → ∀ field : Nat, field < 2 →
      (ptr.toNat + (j * 2 + field + 1) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536) :
    LevelsAt st ptr levels := by
  refine ⟨⟨hLength, hLengthBound⟩, ?_⟩
  intro j hj
  have hRead (field : Nat) (hfield : field < 2) :
      st.mem.read64
          (UInt32.ofNat
            ((ptr.toNat + (j * 2 + (field + 1)) * 8) % 4294967296)) =
        LevelL.word levels[j]! field := by
    have h := hWord j hj field hfield
    unfold levelWord at h
    rw [show j * 2 + field + 1 = j * 2 + (field + 1) by omega] at h
    exact h
  have hFieldBound (field : Nat) (hfield : field < 2) :
      (ptr.toNat + (j * 2 + (field + 1)) * 8) % 4294967296 + 8 ≤
        st.mem.pages * 65536 := by
    have h := hBound j hj field hfield
    rw [show j * 2 + field + 1 = j * 2 + (field + 1) by omega] at h
    exact h
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · simpa [LevelL.word] using hRead 0 (by omega)
  · simpa using hFieldBound 0 (by omega)
  · simpa [LevelL.word] using hRead 1 (by omega)
  · simpa using hFieldBound 1 (by omega)

theorem LevelsAt.frame_region {st st' : Store Unit}
    {ptr capacity : UInt64} {levels : List LevelL}
    (hInput32 : ptr.toNat + fixedArrayBytes levels.length 2 < 4294967296)
    (hHeader : 48 ≤ ptr.toNat)
    (hCapacity : fixedArrayBytes levels.length 2 ≤ capacity.toNat)
    (hPages : st'.mem.pages = st.mem.pages)
    (hBytes : ∀ a : Nat,
      ptr.toNat - 48 ≤ a → a < ptr.toNat + capacity.toNat →
        st'.mem.bytes a = st.mem.bytes a)
    (hInput : LevelsAt st ptr levels) :
    LevelsAt st' ptr levels := by
  obtain ⟨⟨hHead, hHeadBound⟩, hElems⟩ := hInput
  have hRead (word : Nat) (hword : word ≤ levels.length * 2) :
      st'.mem.read64
          (UInt32.ofNat ((ptr.toNat + word * 8) % 4294967296)) =
        st.mem.read64
          (UInt32.ofNat ((ptr.toNat + word * 8) % 4294967296)) := by
    apply Project.Common.read64_congr
    intro i hi
    rw [Project.Common.toUInt32_ofNat_mod_toNat,
      Nat.mod_eq_of_lt (by unfold fixedArrayBytes at hInput32; omega)]
    apply hBytes <;> unfold fixedArrayBytes at hCapacity <;> omega
  refine ⟨⟨(hRead 0 (by omega)).trans hHead, ?_⟩, ?_⟩
  · rwa [hPages]
  · intro j hj
    obtain ⟨h1, h2⟩ := hElems j hj
    refine ⟨⟨(hRead (j * 2 + 1) (by omega)).trans h1.1, ?_⟩,
      ⟨(hRead (j * 2 + 2) (by omega)).trans h2.1, ?_⟩⟩
    · rw [hPages]
      exact h1.2
    · rw [hPages]
      exact h2.2

theorem OwnedLevelArrayAt.frame_region {st st' : Store Unit}
    {ptr capacity : UInt64} {levels : List LevelL}
    (hInput32 : ptr.toNat + fixedArrayBytes levels.length 2 < 4294967296)
    (hHeader : 48 ≤ ptr.toNat)
    (hCapacity : fixedArrayBytes levels.length 2 ≤ capacity.toNat)
    (hPages : st'.mem.pages = st.mem.pages)
    (hBytes : ∀ a : Nat,
      ptr.toNat - 48 ≤ a → a < ptr.toNat + capacity.toNat →
        st'.mem.bytes a = st.mem.bytes a)
    (hInput : OwnedLevelArrayAt st ptr capacity levels) :
    OwnedLevelArrayAt st' ptr capacity levels := by
  exact ⟨hInput.1.frame_region (by omega) hHeader hBytes,
    hInput.2.frame_region hInput32 hHeader hCapacity hPages hBytes⟩

end Project.ClobDepth.Representation
