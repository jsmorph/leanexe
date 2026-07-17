import Project.ClobLimit.LimitResidualAllocFacts

/-!
# Residual copy invariant

The residual book copy writes one flat word at a time into a fresh array.  The
state predicate records the unchanged source representation and every copied
word.  Its advance theorem contains the memory-frame reasoning used by each
loop iteration.
-/

namespace Project.ClobLimit.LimitResidualCopyInvariant

open Wasm Project.Common Project.Clob Project.ClobLimit
  Project.ClobLimit.InternalLoopInvariant
  Project.ClobMatchFuel.Allocation

def copyLoopFrame (base : Locals) (word : Nat) : Locals :=
  { base with
    locals := base.locals.set 39 (.i64 (UInt64.ofNat word))
    values := [] }

structure CopyState (st0 st : Store Unit) (target source capacity : UInt64)
    (os : List OrderL) (word : Nat) : Prop where
  pages : st.mem.pages = st0.mem.pages
  globals : st.globals.globals = st0.globals.globals
  fresh : FreshOrderArrayAt st target capacity
  length : st.mem.read64 target.toUInt32 = UInt64.ofNat (os.length + 1)
  sourceInitial : OrdersAt st0 source os
  sourceCurrent : OrdersAt st source os
  outside : MemEqOutsideFlatWords st0 st target ((os.length + 1) * 5)
  copied : ∀ copied : Nat, copied < word →
    orderWord st target copied = orderWord st0 source copied

def CopyInvariant (st0 : Store Unit) (base : Locals)
    (target source capacity : UInt64) (os : List OrderL) : AssertionF Unit :=
  fun st s =>
    ∃ word : Nat, word ≤ os.length * 5 ∧
      s = copyLoopFrame base word ∧
      CopyState st0 st target source capacity os word

def copyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[39]? with
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
    (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData) (target : UInt64)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data target) :
    copyLoopFrame base 0 = base := by
  have hLocals := hCopy.orderLocals.fields.locals
  have hValues := hCopy.orderLocals.fields.values
  have hCounter : base.locals[39] = .i64 0 := by
    apply Option.some.inj
    calc
      some base.locals[39] = base.locals[39]? :=
        (List.getElem?_eq_getElem (by omega)).symm
      _ = some (.i64 0) := hCopy.counter
  have hSet : base.locals.set 39 (.i64 0) = base.locals := by
    rw [← hCounter]
    exact List.set_getElem_self (by omega)
  cases base
  simp_all [copyLoopFrame]

theorem initial
    (st : Store Unit) (base : Locals) (order : OrderL) (ctx : Context)
    (data : InternalLoopResult.OutputData)
    (hCopy : LimitResidualAlloc.CopyLocalsAt base order ctx data data.g0)
    (hNeed : 8 ≤
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat)
    (hFit32 : data.g0.toNat + 48 +
      (orderArrayBytesU (ctx.result.book.length + 1)).toNat < 4294967296)
    (hRoot : (data.g0 + 48).toNat = data.g0.toNat + 48)
    (hOutput : InternalLoopResult.OutputAt ctx st data) :
    CopyInvariant
      (LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2
        (orderArrayBytesU (ctx.result.book.length + 1))
        (UInt64.ofNat (ctx.result.book.length + 1)))
      base (data.g0 + 48) data.book
      (orderArrayBytesU (ctx.result.book.length + 1)) ctx.result.book
      (LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2
        (orderArrayBytesU (ctx.result.book.length + 1))
        (UInt64.ofNat (ctx.result.book.length + 1))) base := by
  let need := orderArrayBytesU (ctx.result.book.length + 1)
  let length := UInt64.ofNat (ctx.result.book.length + 1)
  let st1 := LimitResidualAlloc.allocStore st data.g0 ctx.expectedG2 need
    length
  have hOwned := LimitResidualAllocFacts.ownedOrderArrayAt_allocStore
    (g2 := ctx.expectedG2) (need := need) (length := length)
    hNeed hFit32 hRoot hOutput.book48 hOutput.book32
    hOutput.bookCapacity hOutput.bookBelow hOutput.bookOwned
  refine ⟨0, Nat.zero_le _, ?_, ?_⟩
  · exact (copyLoopFrame_zero base order ctx data data.g0 hCopy).symm
  · refine {
      pages := rfl
      globals := rfl
      fresh := ?_
      length := ?_
      sourceInitial := ?_
      sourceCurrent := ?_
      outside := ?_
      copied := ?_ }
    · exact LimitResidualAllocFacts.allocStore_fresh st data.g0
        ctx.expectedG2 need length hNeed hFit32 hRoot
    · exact LimitResidualAllocFacts.allocStore_length st data.g0
        ctx.expectedG2 need length
    · simpa only [st1, need, length] using hOwned.2
    · simpa only [st1, need, length] using hOwned.2
    · intro _ _
      rfl
    · intro _ h
      omega

theorem CopyInvariant.at_end
    {st0 st : Store Unit} {base : Locals} {target source capacity : UInt64}
    {os : List OrderL}
    (hInvariant : CopyInvariant st0 base target source capacity os st
      (copyLoopFrame base (os.length * 5)))
    (hLocals : base.locals.length = 53)
    (hTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hTotal64 : os.length * 5 < UInt64.size) :
    CopyState st0 st target source capacity os (os.length * 5) := by
  obtain ⟨word, hWord, hFrame, hState⟩ := hInvariant
  have hCounter := congrArg (fun s : Locals => s.locals[39]?) hFrame
  have hWordEq : UInt64.ofNat os.length * 5 = UInt64.ofNat word := by
    simpa [copyLoopFrame, hLocals] using hCounter
  have hWordNat : word < UInt64.size := by omega
  have hEq := congrArg UInt64.toNat hWordEq
  rw [hTotalU, toNat_ofNat_lt hWordNat] at hEq
  subst word
  exact hState

theorem CopyState.advance
    {st0 st : Store Unit} {target source capacity : UInt64}
    {os : List OrderL} {word : Nat}
    (hState : CopyState st0 st target source capacity os word)
    (hWord : word < os.length * 5)
    (hTarget48 : 48 ≤ target.toNat)
    (hSource32 : source.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hTarget32 : target.toNat + ((os.length + 1) * 5 + 1) * 8 <
      4294967296)
    (hsep : flatWordsDisjoint
      (flatWordsRegion target ((os.length + 1) * 5))
      (flatWordsRegion source (os.length * 5))) :
    CopyState st0 (copyWriteStore st target source word) target source
      capacity os (word + 1) := by
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
    unfold orderWord
    by_cases hCurrent : copied = word
    · subst copied
      simp only [copyWriteStore]
      rw [Mem.read64_write64_same]
      have hSourceCurrent := hState.sourceCurrent.orderWord_eq_flat word hWord
      have hSourceInitial := hState.sourceInitial.orderWord_eq_flat word hWord
      unfold orderWord at hSourceCurrent hSourceInitial
      exact hSourceCurrent.trans hSourceInitial.symm
    · simp only [copyWriteStore]
      rw [read64_write64_ne _ _ _ _ (by
        simp only [toUInt32_ofNat_mod_toNat]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt hTargetLt]
        omega)]
      have hPrevious := hState.copied copied (by omega)
      unfold orderWord at hPrevious
      exact hPrevious

end Project.ClobLimit.LimitResidualCopyInvariant
