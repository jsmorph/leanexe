import Project.ProofKit.FixedArrayAllocate

namespace Project.ProofKit.FixedArrayAllocate

open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit FixedArraySearch
  FixedArrayAllocateNone

def preparedProgram (start : Nat) (stride : UInt64) : Wasm.Program :=
  FixedArraySearch.program start (FixedArrayReuse.program start stride) ++
    [.localGet (start + 5), .constI64 0, .eqI64,
      .iff 0 0 (FixedArrayBump.program start (start + 3) (start + 4) (start + 5) stride) []] ++
    countProgram

theorem preparedProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need stride capacity next count : UInt64) (nodes : List FreeNode)
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
      (counted (allocated store base need stride nodes) count)
      (frame params saved tail need previous current capacity next (root base need nodes)) env) :
    wp module_ (preparedProgram start stride ++ rest) Q store
      (frame params saved tail need 0 (freeHead nodes) capacity next 0) env := by
  subst start
  simp only [preparedProgram, List.append_assoc]
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hNone : takeFirstFit need nodes = none := by
      rw [← takeFirstFitFrom_project 0 need nodes, hTake]
      rfl
    apply noneProgram_spec module_ env store params saved tail _ rfl
      (FixedArrayReuse.program (params.length + saved.length) stride) need capacity next
      nodes hList hNone
    intro previous oldCapacity oldNext
    simp [wp_simp, frame, Nat.add_assoc]
    refine wp_iff_cons rfl ?_
    simp only
    apply FixedArrayBump.program_spec_of_grow _ _ _ _ module_ env store
      (frame params saved tail need previous 0 oldCapacity oldNext 0) base need stride rfl
    · simp [frame, Locals.get, Nat.add_assoc]
    · simp [frame, Locals.validIndex, Nat.add_assoc]
    · exact hGlobal0
    · exact (hBump hTake).1
    · exact hPages
    · exact hMemory32
    · exact (hBump hTake).2
    rw [← Nat.add_assoc params.length saved.length 3,
      ← Nat.add_assoc params.length saved.length 4,
      ← Nat.add_assoc params.length saved.length 5, bump_result]
    simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append, frame]
    apply countProgram_spec module_ env _ _ count rfl
      ((FixedArrayAllocateNone.allocated_count store base need stride).trans hGlobal2) Q rest
    simpa only [allocated, root, hTake, frame] using
      hNext previous 0 (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1)
  | some choice =>
    have hRoot := hList.roots_ne_zero choice.node (takeFirstFitFrom_some_mem hTake)
    apply fitProgram_spec module_ env store params saved tail _ rfl need capacity next stride
      nodes choice hGlobal1 hList hTake
    simp [wp_simp, frame, Nat.add_assoc, hRoot]
    refine wp_iff_cons rfl ?_
    simp [wp_simp]
    have hCount : (fixedArrayAllocFitStore store choice stride).globals.globals[2]? =
        some (.i64 count) := by
      simpa only [allocated, hTake] using (allocated_count store base need stride nodes).trans hGlobal2
    apply countProgram_spec module_ env _ _ count rfl hCount Q rest
    simpa only [allocated, root, hTake, frame, List.cons_append, List.nil_append] using
      hNext choice.previous choice.node.root choice.node.capacity choice.next

#print axioms preparedProgram_spec

end Project.ProofKit.FixedArrayAllocate
