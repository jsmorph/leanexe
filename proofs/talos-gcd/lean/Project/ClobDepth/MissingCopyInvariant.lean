import Project.ClobDepth.MissingFinish
import Project.ClobDepth.LevelCopyInvariant

/-!
# Missing-price copy invariant

The missing-price branch copies the old stride-two level words into a fresh
array before writing the appended level.  The invariant records the copied
prefix and the memory facts needed by the following store phase.
-/

namespace Project.ClobDepth.MissingCopyInvariant

open Wasm Project.Common Project.Clob Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation
  Project.ClobDepth.LevelCopyInvariant

def copyLoopFrame (base : Locals) (word : Nat) : Locals :=
  { base with
    locals := base.locals.set 15 (.i64 (UInt64.ofNat word))
    values := [] }

abbrev CopyState (st0 st : Store Unit) (target source capacity : UInt64)
    (levels : List LevelL) (word : Nat) : Prop :=
  LevelCopyInvariant.CopyState st0 st target source capacity levels
    (levels.length + 1) ((levels.length + 1) * 2) word

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
  LevelCopyInvariant.copyWriteStore st target source word

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
  · exact LevelCopyInvariant.CopyState.initial hFresh hLength hSource

theorem CopyInvariant.at_end
    {st0 st : Store Unit} {base : Locals} {target source capacity : UInt64}
    {levels : List LevelL}
    (hInvariant : CopyInvariant st0 base target source capacity levels st
      (copyLoopFrame base (levels.length * 2)))
    (hLocals : base.locals.length = 26)
    (hTotalU : (UInt64.ofNat levels.length * 2).toNat =
      levels.length * 2)
    (hTotal64 : levels.length * 2 < UInt64.size) :
    CopyState st0 st target source capacity levels (levels.length * 2) := by
  obtain ⟨word, hWord, hFrame, hState⟩ := hInvariant
  have hCounter := congrArg (fun s : Locals => s.locals[15]?) hFrame
  have hWordEq : UInt64.ofNat levels.length * 2 = UInt64.ofNat word := by
    simpa [copyLoopFrame, hLocals] using hCounter
  have hWordNat : word < UInt64.size := by omega
  have hEq := congrArg UInt64.toNat hWordEq
  rw [hTotalU, toNat_ofNat_lt hWordNat] at hEq
  subst word
  exact hState

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
  simpa only [copyWriteStore] using
    LevelCopyInvariant.CopyState.advance hState hWord (by omega) hTarget48
      hSource32 hTarget32 hsep

end Project.ClobDepth.MissingCopyInvariant
