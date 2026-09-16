import Project.EulerRiemann.Program
import Project.EulerRiemann.Memory
import Project.FixedArrayAllocation
import Project.ProofKit.FixedArrayRelease

namespace Project.EulerRiemann.Execution
open Wasm Project.Clob

def releasedStore (store : Store Unit) (root head releases frees : UInt64) : Store Unit :=
  { store with
    mem := (store.mem.write64 (root - 40).toUInt32 0).write64 (root - 8).toUInt32 head
    globals :=
      { globals := ((store.globals.globals.set 4 (.i64 (releases + 1))).set 5
          (.i64 (frees + 1))).set 1 (.i64 root) } }

theorem release_exact (env : HostEnv Unit) (initial : Store Unit)
    (root capacity head releases frees : UInt64) (grid : Array Traversal.Cell)
    (hRoot : 48 ≤ root.toNat) (hHeader : FreshFixedArrayAt initial root capacity 7)
    (hGrid : Memory.GridAt initial root grid)
    (hHead : initial.globals.globals[1]? = some (.i64 head))
    (hReleases : initial.globals.globals[4]? = some (.i64 releases))
    (hFrees : initial.globals.globals[5]? = some (.i64 frees)) :
    TerminatesWith env Project.EulerRiemann.«module» 107 initial [.i64 root]
      (fun final values => values = [] ∧ final = releasedStore initial root head releases frees) := by
  have hBounds := hGrid.1
  have hFits := hGrid.2.1
  exact Project.ProofKit.FixedArrayRelease.exact env Project.EulerRiemann.«module» 107
    initial root capacity head releases frees grid.size 7 (typeIdx := some 107)
    rfl (by decide) (by omega) (by decide) hRoot (by omega) (by omega)
    hHeader hGrid.lengthRead hHead hReleases hFrees

theorem releasedStore_pages (store : Store Unit) (root head releases frees : UInt64) :
    (releasedStore store root head releases frees).mem.pages = store.mem.pages := rfl

theorem releasedStore_memoryCap (store : Store Unit) (root head releases frees : UInt64)
    (module_ : Wasm.Module) (index : Nat) :
    (releasedStore store root head releases frees).memoryCap module_ index =
      store.memoryCap module_ index := rfl

#print axioms release_exact
#print axioms releasedStore_pages
#print axioms releasedStore_memoryCap

end Project.EulerRiemann.Execution
