import Project.ClobDepth.MissingFinish

/-!
# Missing-price copy invariant

The missing-price branch copies the old stride-two level words into a fresh
array before writing the appended level.  The invariant records the copied
prefix and the memory facts needed by the following store phase.
-/

namespace Project.ClobDepth.MissingCopyInvariant

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation

def copyLoopFrame (base : Locals) (word : Nat) : Locals :=
  { base with
    locals := base.locals.set 15 (.i64 (UInt64.ofNat word))
    values := [] }

structure CopyState (st0 st : Store Unit) (target source capacity : UInt64)
    (levels : List LevelL) (word : Nat) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  fresh : FreshFixedArrayAt st target capacity 2
  length : st.mem.read64 target.toUInt32 = UInt64.ofNat (levels.length + 1)
  sourceInitial : LevelsAt st0 source levels
  sourceCurrent : LevelsAt st source levels
  outside : MemEqOutsideFlatWords st0 st target ((levels.length + 1) * 2)
  copied : ∀ copied : Nat, copied < word →
    levelWord st target copied = levelWord st0 source copied

def CopyInvariant (st0 : Store Unit) (base : Locals)
    (target source capacity : UInt64) (levels : List LevelL) :
    AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ levels.length * 2 ∧
      s = copyLoopFrame base word ∧
      CopyState st0 st target source capacity levels word

def copyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[15]? with
  | some (Value.i64 word) => total - word.toNat
  | _ => 0

def copyWriteStore (st : Store Unit) (target source : UInt64)
    (word : Nat) : Store Unit :=
  { st with
    mem := st.mem.write64
      (UInt32.ofNat ((target.toNat + (word + 1) * 8) % 4294967296))
      (st.mem.read64
        (UInt32.ofNat ((source.toNat + (word + 1) * 8) % 4294967296))) }

theorem copyLoopFrame_zero
    (base : Locals)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hCounter : base.locals[15]? = some (.i64 0)) :
    copyLoopFrame base 0 = base := by
  have hCounter' : base.locals[15] = .i64 0 := by
    apply Option.some.inj
    calc
      some base.locals[15] = base.locals[15]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 0) := hCounter
  have hSet : base.locals.set 15 (.i64 0) = base.locals := by
    rw [← hCounter']
    exact List.set_getElem_self (by omega)
  cases base
  simp_all [copyLoopFrame]

theorem initial
    (st : Store Unit) (base : Locals) (target source capacity : UInt64)
    (levels : List LevelL)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hCounter : base.locals[15]? = some (.i64 0))
    (hFresh : FreshFixedArrayAt st target capacity 2)
    (hLength : st.mem.read64 target.toUInt32 =
      UInt64.ofNat (levels.length + 1))
    (hSource : LevelsAt st source levels) :
    CopyInvariant st base target source capacity levels st base := by
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · exact (copyLoopFrame_zero base hLocals hValues hCounter).symm
  · exact {
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
    {levels : List LevelL} {word : Nat}
    (hState : CopyState st0 st target source capacity levels word)
    (hWord : word < levels.length * 2)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 :
      source.toNat + (levels.length * 2 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + ((levels.length + 1) * 2 + 1) * 8 <
      4294967296)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((levels.length + 1) * 2))
      (flatWordsRegion source (levels.length * 2))) :
    CopyState st0 (copyWriteStore st target source word) target source
      capacity levels (word + 1) := by
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

end Project.ClobDepth.MissingCopyInvariant
