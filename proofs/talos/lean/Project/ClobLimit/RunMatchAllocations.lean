import Project.ClobLimit.RunMatchPrepare

/-!
# `runMatch` initial allocations

Function 18 allocates the owner and data roots for an empty trade array before
calling the internal matcher.  This module composes both uses of the proved
allocation block and records their exact store and local frame.
-/

namespace Project.ClobLimit.RunMatchAllocations

open Wasm Project.Clob Project.ClobLimit
  Project.ClobMatchFuel.AllocatorFrame

def firstResultFrame (base : Locals) (root : UInt64) : Locals :=
  { base with locals := base.locals.set 9 (.i64 root), values := [] }

def secondResultFrame (base : Locals) (root qty : UInt64) : Locals :=
  { base with
    locals := (base.locals.set 10 (.i64 root)).set 11 (.i64 qty)
    values := [] }

def firstFrame (bookOwner book : UInt64) (taker : OrderL)
    (os : List OrderL) (g0 : UInt64) : Locals :=
  firstResultFrame
    (RunMatchEmptyAlloc.allocFrame
      (RunMatchPrepare.prepareFrame bookOwner book taker os) g0)
    (g0 + 48)

def allocationsStore (st : Store Unit) (g0 g2 : UInt64) : Store Unit :=
  RunMatchEmptyAlloc.allocStore
    (RunMatchEmptyAlloc.allocStore st g0 g2) (g0 + 56) (g2 + 1)

def finalFrame (bookOwner book : UInt64) (taker : OrderL)
    (os : List OrderL) (g0 : UInt64) : Locals :=
  secondResultFrame
    (RunMatchEmptyAlloc.allocFrame
      (firstFrame bookOwner book taker os g0) (g0 + 56))
    (g0 + 56 + 48) taker.oqty

structure AllocationFacts (before after : Store Unit)
    (book bookCapacity g0 g2 : UInt64) (os : List OrderL) : Prop where
  book : OwnedOrderArrayAt after book bookCapacity os
  owner : OwnedTradeArrayAt after (g0 + 48) 8 []
  trades : OwnedTradeArrayAt after (g0 + 104) 8 []
  pages : after.mem.pages = before.mem.pages
  global0 : after.globals.globals[0]? = some (.i64 (g0 + 112))
  global1 : after.globals.globals[1]? = some (.i64 0)
  global2 : after.globals.globals[2]? = some (.i64 (g2 + 2))
  bytesBefore : ∀ a : Nat, a < g0.toNat →
    after.mem.bytes a = before.mem.bytes a

theorem allocationsStore_facts
    (st : Store Unit) (book bookCapacity g0 g2 : UInt64) (os : List OrderL)
    (hFit32 : g0.toNat + 112 < 4294967296)
    (hFit : g0.toNat + 112 ≤ st.mem.pages * 65536)
    (hBook48 : 48 ≤ book.toNat)
    (hBook32 : book.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hBookCapacity : fixedArrayBytes os.length 5 ≤ bookCapacity.toNat)
    (hBookBelow : book.toNat + bookCapacity.toNat ≤ g0.toNat)
    (hBook : OwnedOrderArrayAt st book bookCapacity os)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2)) :
    AllocationFacts st (allocationsStore st g0 g2)
      book bookCapacity g0 g2 os := by
  let st1 := RunMatchEmptyAlloc.allocStore st g0 g2
  have hG056 : (g0 + 56).toNat = g0.toNat + 56 := by
    rw [UInt64.toNat_add]
    have h56 : (56 : UInt64).toNat = 56 := rfl
    rw [h56]
    omega
  have hRoot1 : (g0 + 48).toNat = g0.toNat + 48 := by
    rw [UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hRoot2 : (g0 + 56 + 48).toNat = g0.toNat + 104 := by
    rw [UInt64.toNat_add, hG056]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    rw [h48]
    omega
  have hHeapValue : g0 + 56 + 56 = g0 + 112 := by
    rw [UInt64.add_assoc]
    rw [show (56 : UInt64) + 56 = 112 by decide]
  have hRoot2Value : g0 + 56 + 48 = g0 + 104 := by
    rw [UInt64.add_assoc]
    rw [show (56 : UInt64) + 48 = 104 by decide]
  have hCounterValue : g2 + 1 + 1 = g2 + 2 := by
    rw [UInt64.add_assoc]
    rw [show (1 : UInt64) + 1 = 2 by decide]
  have hFirstFit32 : g0.toNat + 56 < 4294967296 := by omega
  have hSecondFit32 : (g0 + 56).toNat + 56 < 4294967296 := by
    rw [hG056]
    omega
  have hFirstFit : g0.toNat + 56 ≤ st.mem.pages * 65536 := by omega
  have hSecondFit : (g0 + 56).toNat + 56 ≤ st1.mem.pages * 65536 := by
    rw [hG056, RunMatchEmptyAlloc.allocStore_pages]
    omega
  have hBook1 : OwnedOrderArrayAt st1 book bookCapacity os :=
    RunMatchEmptyAlloc.ownedOrderArrayAt_allocStore hFirstFit32 hBook48
      hBook32 hBookCapacity hBookBelow hBook
  have hBook2 : OwnedOrderArrayAt (allocationsStore st g0 g2)
      book bookCapacity os := by
    apply RunMatchEmptyAlloc.ownedOrderArrayAt_allocStore hSecondFit32
      hBook48 hBook32 hBookCapacity
    · rw [hG056]
      omega
    · exact hBook1
  have hOwner1 : OwnedTradeArrayAt st1 (g0 + 48) 8 [] :=
    RunMatchEmptyAlloc.allocStore_empty_trade st g0 g2 hFirstFit32 hFirstFit
  have hOwner2 : OwnedTradeArrayAt (allocationsStore st g0 g2)
      (g0 + 48) 8 [] := by
    apply RunMatchEmptyAlloc.ownedTradeArrayAt_allocStore hSecondFit32
    · rw [hRoot1]
      omega
    · simp [fixedArrayBytes]
      omega
    · simp [fixedArrayBytes]
    · rw [hRoot1, hG056]
      have h8 : (8 : UInt64).toNat = 8 := rfl
      rw [h8]
    · exact hOwner1
  have hTrades2 : OwnedTradeArrayAt (allocationsStore st g0 g2)
      (g0 + 56 + 48) 8 [] :=
    RunMatchEmptyAlloc.allocStore_empty_trade st1 (g0 + 56) (g2 + 1)
      hSecondFit32 hSecondFit
  refine ⟨hBook2, hOwner2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hRoot2Value] using hTrades2
  · exact (RunMatchEmptyAlloc.allocStore_pages st1 (g0 + 56) (g2 + 1)).trans
      (RunMatchEmptyAlloc.allocStore_pages st g0 g2)
  · have hG0First := RunMatchEmptyAlloc.allocStore_global0 st g0 g2 _ hg0
    have hG0Second := RunMatchEmptyAlloc.allocStore_global0 st1
      (g0 + 56) (g2 + 1) _ hG0First
    simpa only [allocationsStore, st1, hHeapValue] using hG0Second
  · have hG1First := RunMatchEmptyAlloc.allocStore_global1 st g0 g2 0 hg1
    exact RunMatchEmptyAlloc.allocStore_global1 st1
      (g0 + 56) (g2 + 1) 0 hG1First
  · have hG2First := RunMatchEmptyAlloc.allocStore_global2 st g0 g2 _ hg2
    have hG2Second := RunMatchEmptyAlloc.allocStore_global2 st1
      (g0 + 56) (g2 + 1) _ hG2First
    simpa only [allocationsStore, st1, hCounterValue] using hG2Second
  · intro a ha
    rw [allocationsStore]
    rw [RunMatchEmptyAlloc.allocStore_bytes_before st1 (g0 + 56)
      (g2 + 1) a hSecondFit32 (by rw [hG056]; omega)]
    exact RunMatchEmptyAlloc.allocStore_bytes_before st g0 g2 a
      hFirstFit32 ha

set_option Elab.async false in
theorem firstAllocResultProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals) (root : UInt64)
    (hParams : base.params.length = 7)
    (hLocals : base.locals.length = 35)
    (hValues : base.values = [])
    (hRoot : base.get 13 = some (.i64 root))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (firstResultFrame base root) env) :
    wp «module» (RunMatchEntry.firstAllocResultProg ++ rest) Q st base env := by
  simp only [RunMatchEntry.firstAllocResultProg, List.cons_append,
    List.nil_append]
  simp only [Locals.get] at hRoot
  have hRoot' : base.locals[6] = .i64 root := by
    simpa [hParams, hLocals] using hRoot
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, hRoot']
  simpa [firstResultFrame, hValues] using hNext

set_option Elab.async false in
theorem secondAllocResultProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (root qty : UInt64)
    (hParams : base.params.length = 7)
    (hLocals : base.locals.length = 35)
    (hValues : base.values = [])
    (hRoot : base.get 13 = some (.i64 root))
    (hQty : base.get 6 = some (.i64 qty))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st (secondResultFrame base root qty) env) :
    wp «module» (RunMatchEntry.secondAllocResultProg ++ rest) Q st base env := by
  simp only [RunMatchEntry.secondAllocResultProg, List.cons_append,
    List.nil_append]
  simp only [Locals.get] at hRoot hQty
  have hRoot' : base.locals[6] = .i64 root := by
    simpa [hParams, hLocals] using hRoot
  have hQty' : base.params[6] = .i64 qty := by
    simpa [hParams, hLocals] using hQty
  simp (config := { maxSteps := 10000000 }) [wp_simp, hParams, hLocals,
    hValues, hRoot', hQty']
  simpa [secondResultFrame, hValues] using hNext

set_option Elab.async false in
theorem allocationsProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (bookOwner book g0 g2 : UInt64) (taker : OrderL) (os : List OrderL)
    (hFit32 : g0.toNat + 112 < 4294967296)
    (hFit : g0.toNat + 112 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q (allocationsStore st g0 g2)
      (finalFrame bookOwner book taker os g0) env) :
    wp «module»
      (RunMatchEmptyAlloc.allocProg ++ RunMatchEntry.firstAllocResultProg ++
        RunMatchEmptyAlloc.allocProg ++
        RunMatchEntry.secondAllocResultProg ++ rest)
      Q st (RunMatchPrepare.prepareFrame bookOwner book taker os) env := by
  have hG056 : (g0 + 56).toNat = g0.toNat + 56 := by
    rw [UInt64.toNat_add]
    have h56 : (56 : UInt64).toNat = 56 := rfl
    rw [h56]
    omega
  apply RunMatchEmptyAlloc.allocProg_spec env st
    (RunMatchPrepare.prepareFrame bookOwner book taker os) g0 g2
  · simp [RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
      RunMatchPrepare.entryFrame]
  · simp [RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
      RunMatchPrepare.entryFrame]
  · simp [RunMatchPrepare.prepareFrame]
  · omega
  · omega
  · exact hPages
  · exact hg0
  · exact hg1
  · exact hg2
  · apply firstAllocResultProg_spec env
      (RunMatchEmptyAlloc.allocStore st g0 g2)
      (RunMatchEmptyAlloc.allocFrame
        (RunMatchPrepare.prepareFrame bookOwner book taker os) g0)
      (g0 + 48)
    · simp [RunMatchEmptyAlloc.allocFrame, RunMatchPrepare.prepareFrame,
        RunMatchPrepare.prepareLocals, RunMatchPrepare.entryFrame]
    · simp [RunMatchEmptyAlloc.allocFrame, RunMatchPrepare.prepareFrame,
        RunMatchPrepare.prepareLocals, RunMatchPrepare.entryFrame]
    · simp [RunMatchEmptyAlloc.allocFrame, RunMatchPrepare.prepareFrame]
    · simp [Locals.get, RunMatchEmptyAlloc.allocFrame,
        RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
        RunMatchPrepare.entryFrame]
    apply RunMatchEmptyAlloc.allocProg_spec env
      (RunMatchEmptyAlloc.allocStore st g0 g2)
      (firstFrame bookOwner book taker os g0) (g0 + 56) (g2 + 1)
    · simp [firstFrame, firstResultFrame, RunMatchEmptyAlloc.allocFrame,
        RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
        RunMatchPrepare.entryFrame]
    · simp [firstFrame, firstResultFrame, RunMatchEmptyAlloc.allocFrame,
        RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
        RunMatchPrepare.entryFrame]
    · simp [firstFrame, firstResultFrame]
    · rw [hG056]
      omega
    · rw [hG056, RunMatchEmptyAlloc.allocStore_pages]
      omega
    · simpa [RunMatchEmptyAlloc.allocStore_pages] using hPages
    · exact RunMatchEmptyAlloc.allocStore_global0 st g0 g2 _ hg0
    · exact RunMatchEmptyAlloc.allocStore_global1 st g0 g2 0 hg1
    · exact RunMatchEmptyAlloc.allocStore_global2 st g0 g2 _ hg2
    · apply secondAllocResultProg_spec env (allocationsStore st g0 g2)
        (RunMatchEmptyAlloc.allocFrame
          (firstFrame bookOwner book taker os g0) (g0 + 56))
        (g0 + 56 + 48) taker.oqty
      · simp [firstFrame, firstResultFrame, RunMatchEmptyAlloc.allocFrame,
          RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
          RunMatchPrepare.entryFrame]
      · simp [firstFrame, firstResultFrame, RunMatchEmptyAlloc.allocFrame,
          RunMatchPrepare.prepareFrame, RunMatchPrepare.prepareLocals,
          RunMatchPrepare.entryFrame]
      · simp [firstFrame, firstResultFrame, RunMatchEmptyAlloc.allocFrame]
      · simp [Locals.get, firstFrame, firstResultFrame,
          RunMatchEmptyAlloc.allocFrame, RunMatchPrepare.prepareFrame,
          RunMatchPrepare.prepareLocals, RunMatchPrepare.entryFrame]
      · simp [Locals.get, firstFrame, firstResultFrame,
          RunMatchEmptyAlloc.allocFrame, RunMatchPrepare.prepareFrame,
          RunMatchPrepare.prepareLocals, RunMatchPrepare.entryFrame]
      · exact hNext

end Project.ClobLimit.RunMatchAllocations
