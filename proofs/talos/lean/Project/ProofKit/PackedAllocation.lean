import Project.ProofKit.PackedAllocate
import Project.ProofKit.PackedReuse

namespace Project.ProofKit.PackedAllocation
open Wasm Project.Runtime FixedArraySearch FixedArrayAllocateNone

def allocated (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) : Store Unit :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => PackedReuse.reused store choice
  | none => PackedAllocate.allocated store base need

def root (base need : UInt64) (nodes : List FreeNode) : UInt64 :=
  match takeFirstFitFrom 0 need nodes with
  | some choice => choice.node.root
  | none => base + 48

def program (start : Nat) : Wasm.Program :=
  PackedAllocate.program start (PackedReuse.program start)

theorem allocated_count (store : Store Unit) (base need : UInt64) (nodes : List FreeNode) :
    (allocated store base need nodes).globals.globals[2]? = store.globals.globals[2]? := by
  unfold allocated
  split
  · unfold PackedReuse.reused FixedArrayReuse.unlinkStore
    split <;> simp
  · exact PackedAllocate.allocated_count ..

theorem program_spec_available (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need previous current capacity next result count : UInt64) (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < FixedArrayBump.requiredPages base need →
        FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0))
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64, wp module_ rest Q
      (counted (allocated store base need nodes) count)
      (frame params saved tail need previous current capacity next (root base need nodes)) env) :
    wp module_ (program start ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  subst start
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hNone : takeFirstFit need nodes = none := by
      rw [← takeFirstFitFrom_project 0 need nodes, hTake]
      rfl
    apply PackedAllocate.program_spec_available module_ env store params saved tail _ rfl
      (PackedReuse.program (params.length + saved.length))
      base need previous current capacity next result count nodes
      hGlobal0 hGlobal1 hGlobal2 hList hNone (hBump hTake).1 hPages hMemory32 (hBump hTake).2
    intro previous
    simpa only [allocated, root, hTake] using
      hNext previous 0 (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1)
  | some choice =>
    have hRoot := hList.roots_ne_zero choice.node (takeFirstFitFrom_some_mem hTake)
    simp only [program, PackedAllocate.program, List.append_assoc]
    apply initializeProgram_spec module_ env store params saved tail _ rfl need previous current
      capacity next result (freeHead nodes) hGlobal1
    apply PackedReuse.search_spec module_ env store params saved tail _ rfl need capacity next
      nodes choice hGlobal1 hList hTake
    simp [wp_simp, frame, Nat.add_assoc, hRoot]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    have hCount : (PackedReuse.reused store choice).globals.globals[2]? = some (.i64 count) := by
      simpa only [allocated, hTake] using (allocated_count store base need nodes).trans hGlobal2
    apply countProgram_spec module_ env _ _ count rfl hCount Q rest
    simpa only [allocated, root, hTake, frame, List.cons_append, List.nil_append] using
      hNext choice.previous choice.node.root choice.node.capacity choice.next

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need previous current capacity next result count : UInt64) (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64, wp module_ rest Q
      (counted (allocated store base need nodes) count)
      (frame params saved tail need previous current capacity next (root base need nodes)) env) :
    wp module_ (program start ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  exact program_spec_available module_ env store params saved tail start hStart base need previous current
    capacity next result count nodes hGlobal0 hGlobal1 hGlobal2 hList
    (fun h => ⟨(hBump h).1, fun _ => (hBump h).2⟩) hPages hMemory32 Q rest hNext

#print axioms program_spec_available

#print axioms program_spec

theorem root_bounds (store : Store Unit) (base need : UInt64) (nodes : List FreeNode)
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none → base.toNat + 48 + need.toNat ≤ 4294967296) :
    (root base need nodes).toNat + need.toNat ≤ 4294967296 ∧
      (root base need nodes).toNat + need.toNat ≤ (allocated store base need nodes).mem.pages * 65536 := by
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hb := hBump hTake
    have hroot : (base + 48).toNat = base.toNat + 48 := by
      simp only [UInt64.toNat_add, UInt64.toNat_ofNat]
      omega
    simp only [root, allocated, hTake]
    rw [hroot]
    exact ⟨hb, FixedArrayBump.requiredPages_fit store base need⟩
  | some choice =>
    have hb := hList.mem_bounds (takeFirstFitFrom_some_mem hTake)
    have hc := takeFirstFitFrom_some_capacity hTake
    rw [UInt64.le_iff_toNat_le] at hc
    simp only [root, allocated, hTake, PackedReuse.reused_pages]
    constructor <;> omega

#print axioms root_bounds

end Project.ProofKit.PackedAllocation
