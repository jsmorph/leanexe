import Project.ProofKit.PackedCapacity
import Project.ProofKit.PackedAllocation
import Project.ProofKit.PackedFloatFrame

namespace Project.ProofKit.PackedAllocExport
open Wasm Project.Runtime PackedFloatFrame

def function (typeIdx : Option Nat) : Wasm.Function :=
  { params := [.i64], locals := List.replicate 6 (.i64), results := [.i64], typeIdx,
    body := PackedCapacity.program 0 1 ++ PackedAllocation.program 1 ++ [.localGet 6] }

theorem exact (module_ : Wasm.Module) (env : HostEnv Unit) (id : Nat)
    (store : Store Unit) (base bytes count : UInt64) (nodes : List FreeNode)
    {typeIdx : Option Nat}
    (hFunction : module_.funcs[id - module_.imports.length]? = some (function typeIdx))
    (hImport : module_.imports[id]? = none)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 (PackedCapacity.capacity bytes) nodes = none →
      base.toNat + 48 + (PackedCapacity.capacity bytes).toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages base (PackedCapacity.capacity bytes) ≤ store.memoryCap module_ 0)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false) :
    TerminatesWith env module_ id store [.i64 bytes] (fun final values =>
      values = [.i64 (PackedAllocation.root base (PackedCapacity.capacity bytes) nodes)] ∧
      final = FixedArrayAllocateNone.counted
        (PackedAllocation.allocated store base (PackedCapacity.capacity bytes) nodes) count) := by
  refine TerminatesWith.of_wp_entry_for hFunction ?_ hImport
  change wp module_ (PackedCapacity.program 0 1 ++ (PackedAllocation.program 1 ++ [.localGet 6])) _ store
    { params := [.i64 bytes], locals := List.replicate 6 (.i64 0) } env
  apply PackedCapacity.program_spec 0 1 bytes module_ env store _ rfl rfl (by exact Nat.le_refl 1)
    (by change 1 < 1 + 6; decide)
  change wp module_ (PackedAllocation.program 1 ++ [.localGet 6]) _ store
    (FixedArraySearch.frame [.i64 bytes] [] [] (PackedCapacity.capacity bytes) 0 0 0 0 0) env
  apply PackedAllocation.program_spec module_ env store [.i64 bytes] [] [] 1 rfl
    base (PackedCapacity.capacity bytes) 0 0 0 0 0 count nodes
    hGlobal0 hGlobal1 hGlobal2 hList hBump hPages hMemory32
  intro previous current capacity next
  simp [wp_simp, FixedArraySearch.frame, function, Function.numParams]

#print axioms exact

end Project.ProofKit.PackedAllocExport
