import Project.EulerRiemann.AllocationBump
import Project.ClobMatchFuel.BookAllocFitState

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.Clob Project.ClobMatchFuel.BookAllocFit
  Project.ProofKit.Memory

def unlinkStore (store : Store Unit) (choice : FreeChoice) : Store Unit :=
  { store with
    globals := if choice.previous = 0 then
      { globals := store.globals.globals.set 1 (.i64 choice.next) } else store.globals
    mem := unlinkFreeChoice store.mem choice }

theorem unlinkStore_pages (store : Store Unit) (choice : FreeChoice) :
    (unlinkStore store choice).mem.pages = store.mem.pages := by
  unfold unlinkStore unlinkFreeChoice
  split <;> rfl

theorem fitStore_header (store : Store Unit) (choice : FreeChoice)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat ≤ 4294967296) :
    fixedArrayAllocFitStore store choice 7 =
      { unlinkStore store choice with
        mem := fixedArrayHeaderMem (unlinkStore store choice).mem
          (choice.node.root - 48) choice.node.capacity 7 } := by
  simp only [unlinkStore, fixedArrayAllocFitStore, fixedArrayAllocFitMem,
    Project.ProofKit.FixedArrayHeader.from_root _ _ _ _ hRoot hRoot32]

def fitUnlink : Wasm.Program :=
  [.localGet 48, .constI64 0, .eqI64,
    .iff 0 0 [.localGet 51, .globalSet 1]
      [.localGet 48, .constI64 8, .subI64, .wrapI64, .localGet 51, .store64 0]]

theorem sweep_fit_parts : sweepFit = fitUnlink ++
    Project.ProofKit.FixedArrayHeader.program 49 50 7 ++ [.localGet 49, .localSet 52] := rfl

theorem fitUnlink_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need result head : UInt64) (choice : FreeChoice)
    (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hBound : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (unlinkStore store choice)
      (allocationFrame params saved need choice.previous choice.node.root choice.node.capacity
        choice.next result) env) :
    wp Project.EulerRiemann.«module» (fitUnlink ++ rest) Q store
      (allocationFrame params saved need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  unfold fitUnlink
  simp [wp_simp, allocationFrame, hParams, hPrefix]
  refine wp_iff_cons rfl ?_
  by_cases hPrevious : choice.previous = 0
  · simpa [wp_simp, allocationFrame, hParams, hPrefix, hPrevious,
      unlinkStore, unlinkFreeChoice, hGlobalLength, hGlobalRead] using hNext
  · have hWriteBound : (choice.previous.toUInt32 - 8).toNat + 8 ≤
        store.mem.pages * 65536 := by simpa using hBound hPrevious
    simpa [wp_simp, allocationFrame, hParams, hPrefix, hPrevious,
      unlinkStore, unlinkFreeChoice, Nat.reducePow, ← toUInt32_eq_ofNat,
      Nat.not_lt.mpr hWriteBound] using hNext

theorem sweep_fit_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need result head : UInt64) (choice : FreeChoice)
    (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (hPrevious : choice.previous ≠ 0 →
      (choice.previous - 8).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hRoot : 48 ≤ choice.node.root.toNat)
    (hRoot32 : choice.node.root.toNat + choice.node.capacity.toNat ≤ 4294967296)
    (hFit : choice.node.root.toNat + choice.node.capacity.toNat ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (fixedArrayAllocFitStore store choice 7)
      (allocationFrame params saved need choice.previous choice.node.root choice.node.capacity
        choice.next choice.node.root) env) :
    wp Project.EulerRiemann.«module» (sweepFit ++ rest) Q store
      (allocationFrame params saved need choice.previous choice.node.root choice.node.capacity
        choice.next result) env := by
  have hBase : (choice.node.root - 48).toNat = choice.node.root.toNat - 48 :=
    toNat_sub_of_le choice.node.root 48 hRoot
  rw [sweep_fit_parts]
  simp only [List.append_assoc]
  apply fitUnlink_spec env store params saved hParams hPrefix need result head choice
    hGlobal hPrevious
  refine Project.ProofKit.FixedArrayHeader.program_spec _ env _ _ 49 50
    (choice.node.root - 48) choice.node.capacity 7 rfl ?_ ?_ ?_ ?_ _ _ ?_
  · simp [allocationFrame, Locals.get, hParams, hPrefix]
  · simp [allocationFrame, Locals.get, hParams, hPrefix]
  · rw [hBase]
    omega
  · rw [hBase, unlinkStore_pages]
    omega
  · rw [← fitStore_header store choice hRoot (by omega)]
    simpa [wp_simp, allocationFrame, hParams, hPrefix] using hNext

#print axioms unlinkStore_pages
#print axioms fitStore_header
#print axioms sweep_fit_parts
#print axioms fitUnlink_spec
#print axioms sweep_fit_spec
#print axioms freeListAt_fixedArrayAllocFitMem

end Project.EulerRiemann.Execution
