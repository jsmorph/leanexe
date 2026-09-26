import Project.ProofKit.FixedArrayAllocate

/-! Allocation within already available memory does not consult the runtime
memory-growth ceiling.  These rules retain the shared free-list and header
proofs while making that no-growth premise explicit. -/
namespace Project.ProofKit.MemoryGrowth
open Wasm

theorem ensureProgram_in_memory (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pageLocal required : Nat)
    (hMemory32 : module_.memIs64 = false) (hValues : frame.values = [])
    (hLocal : frame.get pageLocal = some (.i64 (UInt64.ofNat required)))
    (hCurrent : store.mem.pages ≤ 65536) (hFit : required ≤ store.mem.pages)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (ensured store required) frame env) :
    wp module_ (ensureProgram pageLocal ++ rest) Q store frame env := by
  have hEmpty : ({ frame with values := [] } : Locals) = frame :=
    Frame.ext _ _ rfl rfl hValues.symm
  have hCurrentNat := Allocation.memoryPages_toNat store.mem.pages hCurrent
  have hRequired64 : required < UInt64.size := by
    change required < 18446744073709551616
    omega
  have hCompare : ¬(UInt32.ofNat store.mem.pages).toUInt64 < UInt64.ofNat required := by
    rw [UInt64.lt_iff_toNat_lt, hCurrentNat, UInt64.toNat_ofNat_of_lt' hRequired64]
    omega
  unfold ensureProgram
  simp only [List.cons_append, List.nil_append, wp_memorySize_cons, sizeValue,
    hMemory32, Bool.false_eq_true, reduceIte, wp_extendUI32_cons,
    UInt64.ofNat_uInt32ToNat, wp_localGet_cons, Frame.withValues_get,
    hLocal, hValues, wp_ltUI64_cons]
  refine wp_iff_cons rfl ?_
  simpa [hCompare, ensured, Nat.not_lt.mpr hFit, hValues, hEmpty] using hNext

end Project.ProofKit.MemoryGrowth

namespace Project.ProofKit.FixedArrayBump
open Wasm Project.Clob FixedArrayFold MemoryGrowth

theorem prepareProgram_in_memory (needLocal topLocal pagesLocal resultLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base need : UInt64) (hValues : frame.values = [])
    (hNeed : frame.get needLocal = some (.i64 need))
    (hOrder : frame.params.length ≤ needLocal ∧ needLocal < topLocal ∧
      topLocal < pagesLocal ∧ pagesLocal < resultLocal ∧ frame.validIndex resultLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hFit : base.toNat + 48 + need.toNat ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (preparedStore store base need)
      (result frame topLocal pagesLocal resultLocal base need) env) :
    wp module_ (prepareProgram needLocal topLocal pagesLocal resultLocal ++ rest) Q store frame env := by
  have hResultBound : resultLocal < frame.params.length + frame.locals.length := hOrder.2.2.2.2
  have hNeedValid : frame.validIndex needLocal := by unfold Locals.validIndex; omega
  have hTopValid : frame.validIndex topLocal := by unfold Locals.validIndex; omega
  have hPagesValid : frame.validIndex pagesLocal := by unfold Locals.validIndex; omega
  let prepared := prefixFrame frame topLocal pagesLocal base need
  have hPreparedTop : prepared.get topLocal = some (.i64 (base + 48 + need)) := by
    apply resultFrame_get_of_ne
    · exact le_trans hOrder.1 (by omega)
    · exact le_trans hOrder.1 (by omega)
    · simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hTopValid
    · omega
    · exact resultFrame_get_result frame topLocal _ (by omega) hTopValid
  have hPreparedPages : prepared.get pagesLocal = some (.i64 (UInt64.ofNat (requiredPages base need))) := by
    rw [requiredPages_word base need hFit32]
    apply resultFrame_get_result
    · exact le_trans hOrder.1 (by omega)
    · simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hPagesValid
  have hPreparedValid : prepared.validIndex resultLocal := by
    simpa only [prepared, prefixFrame, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length] using hOrder.2.2.2.2
  simp only [prepareProgram, List.append_assoc]
  apply prefixProgram_spec needLocal topLocal pagesLocal module_ env store frame base need hValues
    hNeed (by omega) hTopValid (by omega) hPagesValid hGlobal hFit32
  apply ensureProgram_in_memory module_ env store prepared pagesLocal (requiredPages base need)
    hMemory32 rfl hPreparedPages hPages (by unfold requiredPages; omega)
  apply installProgram_spec resultLocal topLocal module_ env _ prepared base (base + 48 + need)
    rfl hPreparedTop (by exact le_trans hOrder.1 (by omega)) hPreparedValid
    (by exact le_trans hOrder.1 (by omega))
    (by simpa only [prepared, prefixFrame, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length] using hTopValid) (by omega)
  · unfold ensured
    split <;> exact hGlobal
  simpa only [preparedStore, result] using hNext

theorem program_in_memory (needLocal topLocal pagesLocal resultLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base need stride : UInt64) (hValues : frame.values = [])
    (hNeed : frame.get needLocal = some (.i64 need))
    (hOrder : frame.params.length ≤ needLocal ∧ needLocal < topLocal ∧
      topLocal < pagesLocal ∧ pagesLocal < resultLocal ∧ frame.validIndex resultLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hFit : base.toNat + 48 + need.toNat ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q (allocated store base need stride)
      (result frame topLocal pagesLocal resultLocal base need) env) :
    wp module_ (program needLocal topLocal pagesLocal resultLocal stride ++ rest) Q store frame env := by
  have hResultBound : resultLocal < frame.params.length + frame.locals.length := hOrder.2.2.2.2
  have hNeedValid : frame.validIndex needLocal := by unfold Locals.validIndex; omega
  have hTopValid : frame.validIndex topLocal := by unfold Locals.validIndex; omega
  have hPagesValid : frame.validIndex pagesLocal := by unfold Locals.validIndex; omega
  let prepared := prefixFrame frame topLocal pagesLocal base need
  have hPreparedNeed : prepared.get needLocal = some (.i64 need) := by
    apply resultFrame_get_of_ne
    · exact le_trans hOrder.1 (by omega)
    · exact hOrder.1
    · simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hNeedValid
    · omega
    · exact resultFrame_get_of_ne frame topLocal needLocal _ _
        (by omega) hOrder.1 hNeedValid (by omega) hNeed
  have hPreparedValid : prepared.validIndex resultLocal := by
    simpa only [prepared, prefixFrame, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length] using hOrder.2.2.2.2
  have hFinalNeed : (result frame topLocal pagesLocal resultLocal base need).get needLocal =
      some (.i64 need) := by
    apply resultFrame_get_of_ne
    · exact le_trans hOrder.1 (by omega)
    · exact hOrder.1
    · simpa only [prepared, prefixFrame, Locals.validIndex, resultFrame_params,
        resultFrame_locals_length] using hNeedValid
    · omega
    · exact hPreparedNeed
  have hFinalRoot : (result frame topLocal pagesLocal resultLocal base need).get resultLocal =
      some (.i64 (base + 48)) :=
    resultFrame_get_result prepared resultLocal _ (by exact le_trans hOrder.1 (by omega)) hPreparedValid
  simp only [program, List.append_assoc]
  apply prepareProgram_in_memory needLocal topLocal pagesLocal resultLocal module_ env store frame
    base need hValues hNeed hOrder hGlobal hFit32 hPages hMemory32 hFit
  apply FixedArrayHeader.program_spec module_ env _ _ resultLocal needLocal base need stride
    rfl hFinalRoot hFinalNeed (by omega)
  · exact le_trans (by omega) (requiredPages_fit store base need)
  · simpa only [allocated, preparedStore, fixedArrayAllocBumpStore]
      using hNext

end Project.ProofKit.FixedArrayBump

namespace Project.ProofKit.FixedArrayAllocateNone
open Wasm Project.Runtime FixedArraySearch

theorem program_in_memory (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat) (hStart : params.length + saved.length = start)
    (fitProgram : Wasm.Program) (base need stride previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes) (hNone : takeFirstFit need nodes = none)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hFit : base.toNat + 48 + need.toNat ≤ store.mem.pages * 65536)
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
  apply FixedArrayBump.program_in_memory _ _ _ _ module_ env store
    (frame params saved tail need previous 0 oldCapacity oldNext 0) base need stride rfl
  · simp [frame, Locals.get, Nat.add_assoc]
  · simp [frame, Locals.validIndex, Nat.add_assoc]
  · exact hGlobal0
  · exact hFit32
  · exact hPages
  · exact hMemory32
  · exact hFit
  rw [← Nat.add_assoc params.length saved.length 3,
    ← Nat.add_assoc params.length saved.length 4,
    ← Nat.add_assoc params.length saved.length 5, bump_result]
  simp only [wp_nil, List.take_zero, List.drop_zero, List.nil_append, frame]
  apply countProgram_spec module_ env _ _ count rfl
    ((allocated_count store base need stride).trans hGlobal2) Q rest
  exact hNext previous

end Project.ProofKit.FixedArrayAllocateNone

namespace Project.ProofKit.FixedArrayAllocate
open Wasm Project.Runtime Project.ClobMatchFuel.BookAllocFit FixedArraySearch FixedArrayAllocateNone

theorem program_in_memory (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit)
    (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need stride previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBump : takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      base.toNat + 48 + need.toNat ≤ store.mem.pages * 65536)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next : UInt64, wp module_ rest Q
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
    apply FixedArrayAllocateNone.program_in_memory module_ env store params saved tail _ rfl
      (FixedArrayReuse.program (params.length + saved.length) stride)
      base need stride previous current capacity next result count nodes
      hGlobal0 hGlobal1 hGlobal2 hList hNone (hBump hTake).1 hPages hMemory32 (hBump hTake).2
    intro previous
    simpa only [allocated, root, hTake] using
      hNext previous 0 (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1)
  | some choice =>
    have hRoot := hList.roots_ne_zero choice.node (takeFirstFitFrom_some_mem hTake)
    simp only [program, FixedArrayAllocateNone.program, List.append_assoc]
    apply initializeProgram_spec module_ env store params saved tail _ rfl need previous current
      capacity next result (freeHead nodes) hGlobal1
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

#print axioms program_in_memory
end Project.ProofKit.FixedArrayAllocate
