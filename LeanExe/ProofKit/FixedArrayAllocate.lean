import LeanExe.ProofKit.FixedArrayAllocateNone
import LeanExe.ProofKit.FixedArraySearchFit

namespace LeanExe.ProofKit.FixedArrayAllocate
open Wasm LeanExe.Runtime FixedArraySearch
  FixedArrayAllocateNone

def allocated (store : Store Unit) (base need stride : UInt64) (nodes : List FreeNode) : Store Unit :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => fixedArrayReuseStore store choice need stride
  | none => FixedArrayBump.allocated store base need stride

def root (base need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => reuseRoot choice need
  | none => base + 48

def program (start : Nat) (stride : UInt64) : Wasm.Program :=
  FixedArrayAllocateNone.program start (FixedArrayReuse.program start stride) stride

theorem allocated_count (store : Store Unit) (base need stride : UInt64)
    (nodes : List FreeNode) :
    (allocated store base need stride nodes).globals.globals[2]? = store.globals.globals[2]? := by
  unfold allocated
  split
  · unfold fixedArrayReuseStore fixedArrayAllocFitStore
    split
    · rfl
    · split <;> simp
  · exact FixedArrayAllocateNone.allocated_count ..

/-- `program_spec` for a request of at most `2 ^ 32` bytes, in a memory of at most 65,535
pages whose cap is at most 65,535 pages: the program traps at `unreachable` or allocates
the block, which ends within `65535 * 65536` when no free block is reused. -/
theorem program_spec_runs (aborts : Bool) (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need stride previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBase : base.toNat ≤ 4294967296) (hNeedBound : need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65535) (hMemory32 : module_.memIs64 = false)
    (hCapBound : store.memoryCap module_ 0 ≤ 65535)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hTrap : aborts = true → ∀ st, Q (.Trap st "unreachable"))
    (hRoom : aborts = false → takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < FixedArrayBump.requiredPages base need →
        FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0))
    (hNext : (takeFirstFitFrom 0 need nodes = none →
        base.toNat + 48 + need.toNat ≤ 4294901760) →
      ∀ previous current capacity next : UInt64, wp module_ rest Q
      (counted (allocated store base need stride nodes) count)
      (frame params saved tail need previous current capacity next (root base need nodes)) env) :
    wp module_ (program start stride ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  subst start
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hNone : takeFirstFit need nodes = none := by
      rw [← takeFirstFitFrom_project 0 need nodes, hTake]
      rfl
    apply FixedArrayAllocateNone.program_spec_runs aborts module_ env store params saved tail _
      rfl (FixedArrayReuse.program (params.length + saved.length) stride)
      base need stride previous current capacity next result count nodes
      hGlobal0 hGlobal1 hGlobal2 hList hNone hBase hNeedBound hPages hMemory32 hCapBound Q rest
      hTrap (fun h => hRoom h hTake)
    intro hFit previous
    simpa only [allocated, root, hTake] using
      hNext (fun _ => hFit) previous 0 (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1)
  | some choice =>
    have hRoot := reuseRoot_ne_zero hList hTake
    simp only [program, FixedArrayAllocateNone.program, List.append_assoc]
    apply initializeProgram_spec module_ env store params saved tail _ rfl need previous current
      capacity next result (freeHead nodes) hGlobal1
    apply fitProgram_spec module_ env store params saved tail _ rfl need capacity next stride
      nodes choice hGlobal1 hList hTake
    simp [wp_simp, frame, Nat.add_assoc, hRoot]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    have hCount : (fixedArrayReuseStore store choice need stride).globals.globals[2]? =
        some (.i64 count) := by
      simpa only [allocated, hTake] using (allocated_count store base need stride nodes).trans hGlobal2
    apply countProgram_spec module_ env _ _ count rfl hCount Q rest
    simpa only [allocated, root, hTake, frame, List.cons_append, List.nil_append] using
      hNext (fun h => by simp [hTake] at h) choice.previous choice.node.root choice.node.capacity choice.next

/-- `program_spec_runs` with the trap allowed. -/
theorem program_spec_or_abort (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need stride previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBase : base.toNat ≤ 4294967296) (hNeedBound : need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65535) (hMemory32 : module_.memIs64 = false)
    (hCapBound : store.memoryCap module_ 0 ≤ 65535)
    (Q : Assertion Unit) (rest : Wasm.Program) (hTrap : ∀ st, Q (.Trap st "unreachable"))
    (hNext : (takeFirstFitFrom 0 need nodes = none →
        base.toNat + 48 + need.toNat ≤ 4294901760) →
      ∀ previous current capacity next : UInt64, wp module_ rest Q
      (counted (allocated store base need stride nodes) count)
      (frame params saved tail need previous current capacity next (root base need nodes)) env) :
    wp module_ (program start stride ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env :=
  program_spec_runs true module_ env store params saved tail start hStart base need stride previous
    current capacity next result count nodes hGlobal0 hGlobal1 hGlobal2 hList hBase hNeedBound
    hPages hMemory32 hCapBound Q rest (fun _ => hTrap) (fun h => nomatch h) hNext

#print axioms allocated_count
#print axioms program_spec_or_abort

end LeanExe.ProofKit.FixedArrayAllocate
