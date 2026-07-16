import Project.ClobMatchFuel.PartialBookAllocCopy
import Project.ClobMatchFuel.BookReplaceFinish

/-!
# Partial-fill book update

This module composes partial-book allocation, complete source copying, and the
five stores that replace the matched order quantity.  Both allocator outcomes
retain their bounds, source ownership, and final outside-payload memory frame.
-/

namespace Project.ClobMatchFuel.PartialBookUpdate

open Wasm Project.Common Project.Runtime Project.Clob Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation
  Project.ClobMatchFuel.AllocatorFrame

def partialBookUpdateProg : Wasm.Program :=
  PartialBookAllocCopy.partialBookAllocCopyProg ++
    BookReplaceFinish.replaceFinishProg

set_option Elab.async false in
theorem partialBookUpdateProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (source sourceCapacity g0 g2 capacity next qty : UInt64)
    (os : List OrderL) (i : Nat) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hSourceLocal : base.locals[57]? = some (.i64 source))
    (hIndexLocal : base.locals[58]? = some (.i64 (UInt64.ofNat i)))
    (hLengthLocal : base.locals[59]? =
      some (.i64 (UInt64.ofNat os.length)))
    (hTotalLocal : base.locals[60]? =
      some (.i64 (UInt64.ofNat os.length * 5)))
    (hOidLocal : base.locals[63]? = some (.i64 os[i]!.oid))
    (hTraderLocal : base.locals[64]? = some (.i64 os[i]!.otrader))
    (hSideLocal : base.locals[65]? = some (.i64 os[i]!.oside))
    (hPriceLocal : base.locals[66]? = some (.i64 os[i]!.oprice))
    (hQtyLocal : base.locals[67]? = some (.i64 qty))
    (hCapacityLocal : base.locals[73]? = some (.i64 capacity))
    (hNextLocal : base.locals[74]? = some (.i64 next))
    (hi : i < os.length)
    (hn : os.length < UInt64.size)
    (hbytes : orderArrayBytes os.length + 7 < UInt64.size)
    (hTotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hTotal64 : os.length * 5 < UInt64.size)
    (htop : (g0 + 48 + orderArrayBytesU os.length).toNat =
      g0.toNat + 48 + (orderArrayBytesU os.length).toNat)
    (hFit32 : g0.toNat + 48 + (orderArrayBytesU os.length).toNat <
      4294967296)
    (hFit : g0.toNat + 48 + (orderArrayBytesU os.length).toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hSource48 : 48 ≤ source.toNat)
    (hSource32 : source.toNat + fixedArrayBytes os.length 5 < 4294967296)
    (hSourceCapacity :
      fixedArrayBytes os.length 5 ≤ sourceCapacity.toNat)
    (hSourceBelow : source.toNat + sourceCapacity.toNat ≤ g0.toNat)
    (hSourceFree :
      FreeListSeparatedFromFixedArray nodes source sourceCapacity)
    (hOwned : OwnedOrderArrayAt st source sourceCapacity os)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hFitDone : ∀ choice : FreeChoice,
      takeFirstFitFrom 0 (orderArrayBytesU os.length) nodes = some choice →
      ∀ st1,
        48 ≤ choice.node.root.toNat →
        choice.node.root.toNat + (os.length * 5 + 1) * 8 < 4294967296 →
        choice.node.root.toNat + (os.length * 5 + 1) * 8 ≤
          (PartialBookAllocFit.bookAllocFitStore st choice).mem.pages *
            65536 →
        OwnedOrderArrayAt (PartialBookAllocFit.bookAllocFitStore st choice)
          source sourceCapacity os →
        OwnedOrderArrayAt
          (BookReplaceStore.replaceOrderStore st1 choice.node.root i os[i]!
            qty)
          choice.node.root choice.node.capacity (Model.setQtyL os i qty) →
        MemEqOutsideFlatWords (PartialBookAllocFit.bookAllocFitStore st choice)
        (BookReplaceStore.replaceOrderStore st1 choice.node.root i os[i]!
            qty)
          choice.node.root (os.length * 5) →
        (BookReplaceStore.replaceOrderStore st1 choice.node.root i os[i]!
            qty).mem.pages =
          (PartialBookAllocFit.bookAllocFitStore st choice).mem.pages →
        (BookReplaceStore.replaceOrderStore st1 choice.node.root i os[i]!
            qty).globals.globals =
          (PartialBookAllocFit.bookAllocFitStore st choice).globals.globals.set
            2 (.i64 (g2 + 1)) →
        wp «module» rest Q
          (BookReplaceStore.replaceOrderStore st1 choice.node.root i os[i]!
            qty)
          (BookReplaceFinish.replaceResultFrame
            (PartialBookAllocCopy.fitFrame base os.length choice)
            choice.node.root (os.length * 5)) env)
    (hBumpDone : ∀ previous : UInt64, ∀ st1,
      48 ≤ (g0 + 48).toNat →
      (g0 + 48).toNat + (os.length * 5 + 1) * 8 < 4294967296 →
      (g0 + 48).toNat + (os.length * 5 + 1) * 8 ≤
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length)).mem.pages * 65536 →
      OwnedOrderArrayAt
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length)) source sourceCapacity os →
      OwnedOrderArrayAt
        (BookReplaceStore.replaceOrderStore st1 (g0 + 48) i os[i]! qty)
        (g0 + 48) (orderArrayBytesU os.length) (Model.setQtyL os i qty) →
      MemEqOutsideFlatWords
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length))
        (BookReplaceStore.replaceOrderStore st1 (g0 + 48) i os[i]! qty)
        (g0 + 48) (os.length * 5) →
      (BookReplaceStore.replaceOrderStore st1 (g0 + 48) i os[i]!
          qty).mem.pages =
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length)).mem.pages →
      (BookReplaceStore.replaceOrderStore st1 (g0 + 48) i os[i]!
          qty).globals.globals =
        (PartialBookAllocBump.bookAllocBumpStore st g0
          (orderArrayBytesU os.length)).globals.globals.set
            2 (.i64 (g2 + 1)) →
      wp «module» rest Q
        (BookReplaceStore.replaceOrderStore st1 (g0 + 48) i os[i]! qty)
        (BookReplaceFinish.replaceResultFrame
          (PartialBookAllocCopy.bumpFrame base os.length g0 previous)
          (g0 + 48) (os.length * 5)) env) :
    wp «module» (partialBookUpdateProg ++ rest) Q st base env := by
  unfold partialBookUpdateProg
  rw [List.append_assoc]
  apply PartialBookAllocCopy.partialBookAllocCopyProg_spec env st base source
    sourceCapacity g0 g2 capacity next os nodes hParams hLocals hValues
    hSourceLocal hLengthLocal hTotalLocal hCapacityLocal hNextLocal hn hbytes
    hTotalU hTotal64 htop hFit32 hFit hPages hSource48 hSource32
    hSourceCapacity hSourceBelow hSourceFree hOwned hg0 hg1 hg2 hList Q
    (BookReplaceFinish.replaceFinishProg ++ rest)
  · intro choice hTake st1 hTarget48 hTarget32 hTargetFit hOwnedSource hInv
      hTargetOrders
    have hState := hInv
    obtain ⟨_, _, _, hCopyPages, hCopyGlobals, _, _, _, _, _⟩ := hState
    apply BookReplaceFinish.replaceFinishProg_spec env
      (PartialBookAllocFit.bookAllocFitStore st choice) st1
      (PartialBookAllocCopy.fitFrame base os.length choice) choice.node.root
      source g2 choice.node.capacity qty os i
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame] using hParams
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.length_set] using
        hLocals
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hIndexLocal
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hOidLocal
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hTraderLocal
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hSideLocal
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hPriceLocal
    · simpa [PartialBookAllocCopy.fitFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hQtyLocal
    · exact hi
    · exact hTarget48
    · exact hTarget32
    · exact hInv
    · exact hTargetOrders
    · intro hTargetFinal hFreshFinal hOutsideFinal
      exact hFitDone choice hTake st1 hTarget48 hTarget32 hTargetFit
        hOwnedSource ⟨hFreshFinal, hTargetFinal⟩ hOutsideFinal
        (by simpa [BookReplaceStore.replaceOrderStore] using hCopyPages)
        (by simpa [BookReplaceStore.replaceOrderStore] using hCopyGlobals)
  · intro previous st1 hTarget48 hTarget32 hTargetFit hOwnedSource hInv
      hTargetOrders
    have hState := hInv
    obtain ⟨_, _, _, hCopyPages, hCopyGlobals, _, _, _, _, _⟩ := hState
    apply BookReplaceFinish.replaceFinishProg_spec env
      (PartialBookAllocBump.bookAllocBumpStore st g0
        (orderArrayBytesU os.length)) st1
      (PartialBookAllocCopy.bumpFrame base os.length g0 previous) (g0 + 48)
      source g2 (orderArrayBytesU os.length) qty os i
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame] using hParams
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.length_set] using
        hLocals
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hIndexLocal
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hOidLocal
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hTraderLocal
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hSideLocal
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hPriceLocal
    · simpa [PartialBookAllocCopy.bumpFrame,
        PartialBookAllocSearch.bookAllocSearchFrame, List.getElem?_set] using
        hQtyLocal
    · exact hi
    · exact hTarget48
    · exact hTarget32
    · exact hInv
    · exact hTargetOrders
    · intro hTargetFinal hFreshFinal hOutsideFinal
      exact hBumpDone previous st1 hTarget48 hTarget32 hTargetFit
        hOwnedSource ⟨hFreshFinal, hTargetFinal⟩ hOutsideFinal
        (by simpa [BookReplaceStore.replaceOrderStore] using hCopyPages)
        (by simpa [BookReplaceStore.replaceOrderStore] using hCopyGlobals)

end Project.ClobMatchFuel.PartialBookUpdate
