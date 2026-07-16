import Project.ClobMatchFuel.PartialBookAllocPrepare

/-!
# Complete partial-fill book allocation

This module composes capacity preparation, first-fit search, and bump fallback
for the partial-fill book allocator.  Its theorem exposes the exact store and local
frame for either allocator outcome.  Later branch proofs can establish fresh
headers and free-list frames from the selected outcome without reducing the
allocator instructions again.
-/

namespace Project.ClobMatchFuel.PartialBookAlloc

open Wasm Project.Common Project.Clob Project.Runtime Project.ClobMatchFuel
  Project.ClobMatchFuel.Allocation

def partialBookAllocProg : Wasm.Program :=
  PartialBookAllocPrepare.partialBookAllocPrepareProg ++
    PartialBookAllocBump.bookAllocNoFitProg

set_option Elab.async false in
theorem partialBookAllocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g0 capacity next : UInt64) (nodes : List FreeNode)
    (hParams : base.params.length = 9)
    (hLocals : base.locals.length = 76)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[59]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[73]? = some (.i64 capacity))
    (hNextLocal : base.locals[74]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : orderArrayBytes n + 7 < UInt64.size)
    (htop : (g0 + 48 + orderArrayBytesU n).toNat =
      g0.toNat + 48 + (orderArrayBytesU n).toNat)
    (hFit32 : g0.toNat + 48 + (orderArrayBytesU n).toNat < 4294967296)
    (hFit : g0.toNat + 48 + (orderArrayBytesU n).toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt st.mem nodes)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hFitDone : ∀ choice : FreeChoice,
      takeFirstFitFrom 0 (orderArrayBytesU n) nodes = some choice →
      wp «module» rest Q (PartialBookAllocFit.bookAllocFitStore st choice)
        (PartialBookAllocSearch.bookAllocSearchFrame base (orderArrayBytesU n)
          choice.previous choice.node.root choice.node.capacity choice.next
          choice.node.root) env)
    (hBumpDone : ∀ previous : UInt64,
      wp «module» rest Q
        (PartialBookAllocBump.bookAllocBumpStore st g0 (orderArrayBytesU n))
        (PartialBookAllocSearch.bookAllocSearchFrame base (orderArrayBytesU n)
          previous 0 (g0 + 48 + orderArrayBytesU n)
          ((g0 + 48 + orderArrayBytesU n - 1) / 65536 + 1)
          (g0 + 48)) env) :
    wp «module» (partialBookAllocProg ++ rest) Q st base env := by
  have hNeed8 : 8 ≤ (orderArrayBytesU n).toNat := by
    rw [fixedArrayBytesU_toNat n 5 hn (by decide) (by
      change fixedArrayBytes n 5 + 7 < UInt64.size at hbytes
      omega)]
    unfold fixedArrayBytes
    omega
  unfold partialBookAllocProg PartialBookAllocBump.bookAllocNoFitProg
  rw [List.append_assoc, List.append_assoc]
  apply PartialBookAllocPrepare.partialBookAllocPrepareProg_spec env st base n
    (freeHead nodes) capacity next hParams hLocals hValues hLengthLocal
    hCapacityLocal hNextLocal hn hbytes hg1 Q
    (PartialBookAllocSearch.bookAllocSearchProg ++
      PartialBookAllocBump.bookAllocBumpProg ++ rest)
  cases hChoice : takeFirstFitFrom 0 (orderArrayBytesU n) nodes with
  | none =>
      have hNoFit : takeFirstFit (orderArrayBytesU n) nodes = none := by
        have hProject := takeFirstFitFrom_project 0 (orderArrayBytesU n) nodes
        rw [hChoice] at hProject
        exact hProject.symm
      exact PartialBookAllocBump.bookAllocNoFitProg_spec env st base g0
        (orderArrayBytesU n) capacity next nodes hParams hLocals hValues
        hNeed8 htop hFit32 hFit hPages hg0 hList hNoFit Q rest hBumpDone
  | some choice =>
      apply PartialBookAllocFit.bookAllocSearchProg_fit env st base
        (orderArrayBytesU n) capacity next nodes choice hParams hLocals
        hValues hg1 hList hChoice Q
        (PartialBookAllocBump.bookAllocBumpProg ++ rest)
      have hChoiceRoot : choice.node.root ≠ 0 :=
        hList.roots_ne_zero choice.node (takeFirstFitFrom_some_mem hChoice)
      exact PartialBookAllocBump.bookAllocBumpProg_skip env
        (PartialBookAllocFit.bookAllocFitStore st choice) base
        (orderArrayBytesU n) choice.previous choice.node.root
        choice.node.capacity choice.next choice.node.root hParams hLocals
        hValues hChoiceRoot Q rest (hFitDone choice hChoice)

end Project.ClobMatchFuel.PartialBookAlloc
