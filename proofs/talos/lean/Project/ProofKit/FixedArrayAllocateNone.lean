import Project.ProofKit.FixedArraySearchNone
import Project.ProofKit.FixedArrayBump

namespace Project.ProofKit.FixedArrayAllocateNone
open Wasm Project.Runtime FixedArraySearch

def initializeProgram (start : Nat) : Wasm.Program :=
  [.constI64 0, .localSet (start + 5), .constI64 0, .localSet (start + 1),
    .globalGet 1, .localSet (start + 2)]

def countProgram : Wasm.Program :=
  [.globalGet 2, .constI64 1, .addI64, .globalSet 2]

def counted (store : Store Unit) (count : UInt64) : Store Unit :=
  { store with globals := { globals := store.globals.globals.set 2 (.i64 (count + 1)) } }

def program (start : Nat) (fitProgram : Wasm.Program) (stride : UInt64) : Wasm.Program :=
  initializeProgram start ++ FixedArraySearch.program start fitProgram ++
    [.localGet (start + 5), .constI64 0, .eqI64,
      .iff 0 0 (FixedArrayBump.program start (start + 3) (start + 4) (start + 5) stride) []] ++
    countProgram

theorem initializeProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (params saved tail : List Wasm.Value)
    (start : Nat) (hStart : params.length + saved.length = start)
    (need previous current capacity next result head : UInt64)
    (hGlobal : store.globals.globals[1]? = some (.i64 head))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (frame params saved tail need 0 head capacity next 0) env) :
    wp module_ (initializeProgram start ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  subst start
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  simpa [initializeProgram, wp_simp, frame, Nat.add_assoc, hGlobalLength, hGlobalRead] using hNext

theorem countProgram_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (locals : Locals) (count : UInt64) (hValues : locals.values = [])
    (hGlobal : store.globals.globals[2]? = some (.i64 count))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (counted store count) locals env) :
    wp module_ (countProgram ++ rest) Q store locals env := by
  obtain ⟨hGlobalLength, hGlobalRead⟩ := List.getElem_of_getElem? hGlobal
  have hEmpty : { locals with values := [] } = locals := Frame.ext _ _ rfl rfl hValues.symm
  simpa [countProgram, wp_simp, counted, hValues, hEmpty, hGlobalLength, hGlobalRead] using hNext

theorem bump_result (params saved tail : List Wasm.Value)
    (need previous current capacity next result base : UInt64) :
    FixedArrayBump.result (frame params saved tail need previous current capacity next result)
      (params.length + saved.length + 3) (params.length + saved.length + 4)
      (params.length + saved.length + 5) base need =
    frame params saved tail need previous current (base + 48 + need)
      ((base + 48 + need - 1) / 65536 + 1) (base + 48) := by
  simp [FixedArrayBump.result, FixedArrayBump.prefixFrame, FixedArrayFold.resultFrame,
    frame, Nat.add_assoc]

theorem allocated_count (store : Store Unit) (base need stride : UInt64) :
    (FixedArrayBump.allocated store base need stride).globals.globals[2]? =
      store.globals.globals[2]? := by
  unfold FixedArrayBump.allocated Project.Clob.fixedArrayAllocBumpStore MemoryGrowth.ensured
  split <;> simp [MemoryGrowth.grown]

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (fitProgram : Wasm.Program) (base need stride previous current capacity next result count : UInt64)
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
      (counted (FixedArrayBump.allocated store base need stride) count)
      (frame params saved tail need previous 0 (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) (base + 48)) env) :
    wp module_ (program start fitProgram stride ++ rest) Q store
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
  apply FixedArrayBump.program_spec _ _ _ _ module_ env store
    (frame params saved tail need previous 0 oldCapacity oldNext 0) base need stride rfl
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
  simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append, frame]
  apply countProgram_spec module_ env _ _ count rfl
    ((allocated_count store base need stride).trans hGlobal2) Q rest
  exact hNext previous

#print axioms initializeProgram_spec
#print axioms countProgram_spec
#print axioms bump_result
#print axioms allocated_count
#print axioms program_spec

end Project.ProofKit.FixedArrayAllocateNone
