import Project.ProofKit.FixedArrayAllocateNone
import Project.ProofKit.PackedHeader

namespace Project.ProofKit.PackedAllocate
open Wasm Project.Runtime FixedArraySearch FixedArrayAllocateNone

def program (start : Nat) (fitProgram : Wasm.Program) : Wasm.Program :=
  initializeProgram start ++ FixedArraySearch.program start fitProgram ++
    [.localGet (start + 5), .constI64 0, .eqI64,
      .iff 0 0 (FixedArrayBump.prepareProgram start (start + 3) (start + 4) (start + 5) ++
        PackedHeader.program (start + 5) start) []] ++ countProgram

def allocated (store : Store Unit) (base need : UInt64) : Store Unit :=
  let prepared := FixedArrayBump.preparedStore store base need
  { prepared with mem := PackedHeader.headerMem prepared.mem base need }

theorem allocated_count (store : Store Unit) (base need : UInt64) :
    (allocated store base need).globals.globals[2]? = store.globals.globals[2]? := by
  unfold allocated FixedArrayBump.preparedStore MemoryGrowth.ensured
  split <;> simp [MemoryGrowth.grown]

theorem program_spec_available (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (fitProgram : Wasm.Program) (base need previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes) (hNone : takeFirstFit need nodes = none)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hCap : store.mem.pages < FixedArrayBump.requiredPages base need →
      FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous : UInt64, wp module_ rest Q
      (counted (allocated store base need) count)
      (frame params saved tail need previous 0 (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) (base + 48)) env) :
    wp module_ (program start fitProgram ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  subst start
  simp only [program, List.append_assoc]
  apply initializeProgram_spec module_ env store params saved tail _ rfl need previous current
    capacity next result (freeHead nodes) hGlobal1
  apply noneProgram_spec module_ env store params saved tail _ rfl fitProgram need capacity next
    nodes hList hNone
  intro previous oldCapacity oldNext
  simp [wp_simp, frame, Nat.add_assoc]
  refine wp_iff_cons rfl ?_
  simp only
  apply FixedArrayBump.prepareProgram_spec_available _ _ _ _ module_ env store
    (frame params saved tail need previous 0 oldCapacity oldNext 0) base need rfl
  · simp [frame, Locals.get, Nat.add_assoc]
  · simp [frame, Locals.validIndex, Nat.add_assoc]
  · exact hGlobal0
  · exact hFit32
  · exact hPages
  · exact hMemory32
  · exact hCap
  rw [← Nat.add_assoc params.length saved.length 3,
    ← Nat.add_assoc params.length saved.length 4,
    ← Nat.add_assoc params.length saved.length 5, bump_result]
  apply PackedHeader.program_spec module_ env _ _ _ _ base need rfl
  · simp [frame, Locals.get, Nat.add_assoc]
  · simp [frame, Locals.get, Nat.add_assoc]
  · omega
  · exact le_trans (by omega) (FixedArrayBump.requiredPages_fit store base need)
  simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append, frame]
  apply countProgram_spec module_ env _ _ count rfl
    ((allocated_count store base need).trans hGlobal2) Q rest
  exact hNext previous

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (fitProgram : Wasm.Program) (base need previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes) (hNone : takeFirstFit need nodes = none)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hCap : FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous : UInt64, wp module_ rest Q
      (counted (allocated store base need) count)
      (frame params saved tail need previous 0 (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) (base + 48)) env) :
    wp module_ (program start fitProgram ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  exact program_spec_available module_ env store params saved tail start hStart fitProgram base need
    previous current capacity next result count nodes hGlobal0 hGlobal1 hGlobal2 hList hNone
    hFit32 hPages hMemory32 (fun _ => hCap) Q rest hNext

#print axioms program_spec_available

#print axioms program_spec

end Project.ProofKit.PackedAllocate
