import Project.EulerRiemann.AllocationSearchFit

namespace Project.EulerRiemann.Execution
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit

def allocatedStore (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    Store Unit :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => fixedArrayAllocFitStore store choice 7
  | none => bumpStore store base need

def allocatedRoot (base need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.node.root
  | none => base + 48

def allocationInit : Wasm.Program :=
  [.constI64 0, .localSet 52, .constI64 0, .localSet 48, .globalGet 1, .localSet 49]

def allocationCore : Wasm.Program :=
  [.block 0 0 [.loop 0 0 sweepSearch],
    .localGet 52, .constI64 0, .eqI64, .iff 0 0 sweepBump []]

def allocationCount : Wasm.Program :=
  [.globalGet 2, .constI64 1, .addI64, .globalSet 2]

def countedStore (store : Store Unit) (count : UInt64) : Store Unit :=
  { store with globals := { globals := store.globals.globals.set 2 (.i64 (count + 1)) } }

theorem sweep_allocation_shape : (func70.drop 24).take 15 =
    allocationInit ++ allocationCore ++ allocationCount := rfl

theorem allocationInit_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (need previous current capacity next result head : UInt64)
    (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q store
      (allocationFrame params saved need 0 head capacity next 0) env) :
    wp Project.EulerRiemann.«module» (allocationInit ++ rest) Q store
      (allocationFrame params saved need previous current capacity next result) env := by
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  simpa [allocationInit, wp_simp, allocationFrame, hParams, hPrefix,
    hGlobalLength, hGlobalRead] using hNext

theorem allocationCount_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (count : UInt64) (hValues : frame.values = [])
    (hGlobal : store.globals.globals[2]? = some (.i64 count))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.EulerRiemann.«module» rest Q (countedStore store count) frame env) :
    wp Project.EulerRiemann.«module» (allocationCount ++ rest) Q store frame env := by
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  have hEmpty : { frame with values := [] } = frame :=
    Project.ProofKit.Frame.ext _ _ rfl rfl hValues.symm
  simpa [allocationCount, wp_simp, countedStore, hValues, hEmpty,
    hGlobalLength, hGlobalRead] using hNext

theorem allocatedStore_count (store : Store Unit) (base need : UInt64)
    (nodes : List FreeNode) :
    (allocatedStore store base need nodes).globals.globals[2]? = store.globals.globals[2]? := by
  unfold allocatedStore
  split
  · unfold fixedArrayAllocFitStore
    split <;> simp
  · rw [bumpStore_globals]
    simp

theorem allocationCore_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (base need capacity next : UInt64) (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      bumpPages base need ≤ store.memoryCap Project.EulerRiemann.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.EulerRiemann.«module» rest Q (allocatedStore store base need nodes)
        (allocationFrame params saved need previous current capacity next
          (allocatedRoot base need nodes)) env) :
    wp Project.EulerRiemann.«module» (allocationCore ++ rest) Q store
      (allocationFrame params saved need 0 (freeHead nodes) capacity next 0) env := by
  change wp _ ([.block 0 0 [.loop 0 0 sweepSearch]] ++
    [.localGet 52, .constI64 0, .eqI64, .iff 0 0 sweepBump []] ++ rest) _ _ _ _
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hNone : takeFirstFit need nodes = none := by
      rw [← takeFirstFitFrom_project 0 need nodes, hTake]
      rfl
    obtain ⟨hFit32, hCap⟩ := hBump hTake
    apply search_none_spec env store params saved hParams hPrefix need capacity next nodes
      hList hNone
    intro previous oldCapacity oldNext
    simp [wp_simp, allocationFrame, hParams, hPrefix]
    refine wp_iff_cons rfl ?_
    simp only
    apply sweep_bump_spec env store params saved hParams hPrefix base need previous 0
      oldCapacity oldNext 0 hGlobal0 hFit32 hPages hCap
    simpa [wp_simp, allocatedStore, allocatedRoot, hTake, allocationFrame] using
      hNext previous 0 (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1)
  | some choice =>
    have hRoot := hList.roots_ne_zero choice.node (takeFirstFitFrom_some_mem hTake)
    apply search_fit_spec env store params saved hParams hPrefix need capacity next nodes
      choice hGlobal1 hList hTake
    simp [wp_simp, allocationFrame, hParams, hPrefix, hRoot]
    refine wp_iff_cons rfl ?_
    simpa [wp_simp, allocatedStore, allocatedRoot, hTake, allocationFrame] using
      hNext choice.previous choice.node.root choice.node.capacity choice.next

theorem allocation_spec (env : HostEnv Unit) (store : Store Unit)
    (params saved : List Wasm.Value) (hParams : params.length = 5)
    (hPrefix : saved.length = 42) (base need previous current capacity next result count : UInt64)
    (nodes : List FreeNode) (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      bumpPages base need ≤ store.memoryCap Project.EulerRiemann.«module» 0)
    (hPages : store.mem.pages ≤ 65536) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64,
      wp Project.EulerRiemann.«module» rest Q
        (countedStore (allocatedStore store base need nodes) count)
        (allocationFrame params saved need previous current capacity next
          (allocatedRoot base need nodes)) env) :
    wp Project.EulerRiemann.«module» ((func70.drop 24).take 15 ++ rest) Q store
      (allocationFrame params saved need previous current capacity next result) env := by
  rw [sweep_allocation_shape]
  simp only [List.append_assoc]
  apply allocationInit_spec env store params saved hParams hPrefix need previous current
    capacity next result (freeHead nodes) hGlobal1
  apply allocationCore_spec env store params saved hParams hPrefix base need capacity next
    nodes hGlobal0 hGlobal1 hList hBump hPages
  intro previous current capacity next
  exact allocationCount_spec env _ _ count rfl
    ((allocatedStore_count store base need nodes).trans hGlobal2) Q rest
    (hNext previous current capacity next)

#print axioms sweep_allocation_shape
#print axioms allocationInit_spec
#print axioms allocationCount_spec
#print axioms allocatedStore_count
#print axioms allocationCore_spec
#print axioms allocation_spec

end Project.EulerRiemann.Execution
