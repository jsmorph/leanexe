import LeanExe.ProofKit.AlignedReuse
import LeanExe.ProofKit.FixedArrayAllocate

/-!
`FixedArrayAllocate.program`, the allocation of `alloc`, under `wpA`.  The bump allocation
prepares `top` and memory with code that makes no 64-bit access, whose `wp` specifications apply
through `wpA_append_accessFree`, and then writes the header at the old `top`, so its stores are
aligned when `top` is.  The search and the reuse of a free block are the ports of the reuse
module.  The counter update and the initialization of the search's locals make no 64-bit access.
-/

namespace LeanExe.ProofKit.FixedArrayBump
open Wasm LeanExe.ProofKit FixedArrayFold MemoryGrowth

theorem program_spec_of_growA (needLocal topLocal pagesLocal resultLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base need stride : UInt64) (hValues : frame.values = [])
    (hNeed : frame.get needLocal = some (.i64 need))
    (hOrder : frame.params.length ≤ needLocal ∧ needLocal < topLocal ∧
      topLocal < pagesLocal ∧ pagesLocal < resultLocal ∧ frame.validIndex resultLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hCap : store.mem.pages < requiredPages base need →
      requiredPages base need ≤ store.memoryCap module_ 0)
    (hBaseAl : base.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q (allocated store base need stride)
      (result frame topLocal pagesLocal resultLocal base need) env) :
    wpA module_ (program needLocal topLocal pagesLocal resultLocal stride ++ rest) Q store frame
      env := by
  have hResultBound : resultLocal < frame.params.length + frame.locals.length := hOrder.2.2.2.2
  have hNeedValid : frame.validIndex needLocal := by unfold Locals.validIndex; omega
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
    resultFrame_get_result prepared resultLocal _ (by exact le_trans hOrder.1 (by omega))
      hPreparedValid
  simp only [program, List.append_assoc]
  refine wpA_append_accessFree (by rfl) ?_
  rw [← List.append_nil (prepareProgram _ _ _ _)]
  refine prepareProgram_spec_available needLocal topLocal pagesLocal resultLocal module_ env store
    frame base need hValues hNeed hOrder hGlobal hFit32 hPages hMemory32 hCap _ _ (wp_nil.mpr ?_)
  apply FixedArrayHeader.program_specA module_ env _ _ resultLocal needLocal base need stride
    rfl hFinalRoot hFinalNeed (by omega)
  · exact le_trans (by omega) (requiredPages_fit store base need)
  · exact hBaseAl
  · simpa only [allocated, preparedStore, fixedArrayAllocBumpStore]
      using hNext

/-- `program_spec_runs` under `wpA`, for a `top` that is a multiple of 8. -/
theorem program_spec_runsA (aborts : Bool) (needLocal topLocal pagesLocal resultLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base need stride : UInt64) (hValues : frame.values = [])
    (hNeed : frame.get needLocal = some (.i64 need))
    (hOrder : frame.params.length ≤ needLocal ∧ needLocal < topLocal ∧
      topLocal < pagesLocal ∧ pagesLocal < resultLocal ∧ frame.validIndex resultLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hBase : base.toNat ≤ 4294967296) (hNeedBound : need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65535) (hMemory32 : module_.memIs64 = false)
    (hCapBound : store.memoryCap module_ 0 ≤ 65535) (hBaseAl : base.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hTrap : aborts = true → ∀ st, Q (.Trap st "unreachable"))
    (hRoom : aborts = false → base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < requiredPages base need →
        requiredPages base need ≤ store.memoryCap module_ 0))
    (hNext : base.toNat + 48 + need.toNat ≤ 4294901760 →
      wpA module_ rest Q (allocated store base need stride)
        (result frame topLocal pagesLocal resultLocal base need) env) :
    wpA module_ (program needLocal topLocal pagesLocal resultLocal stride ++ rest) Q store frame
      env := by
  by_cases hOk : base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < requiredPages base need →
        requiredPages base need ≤ store.memoryCap module_ 0)
  · have hTight : base.toNat + 48 + need.toNat ≤ 4294901760 := by
      have hRequired : requiredPages base need ≤ 65535 := by
        by_cases hLess : store.mem.pages < requiredPages base need
        · exact (hOk.2 hLess).trans hCapBound
        · omega
      unfold requiredPages at hRequired
      omega
    exact program_spec_of_growA needLocal topLocal pagesLocal resultLocal module_ env store frame
      base need stride hValues hNeed hOrder hGlobal hOk.1 (by omega) hMemory32 hOk.2 hBaseAl Q
      rest (hNext hTight)
  cases aborts
  · exact absurd (hRoom rfl) hOk
  have hTrap := hTrap rfl
  have hAbort : store.mem.pages < requiredPages base need ∧
      store.memoryCap module_ 0 < requiredPages base need := by
    by_cases hFit : base.toNat + 48 + need.toNat ≤ 4294967296
    · have hGrow := (not_and.mp hOk) hFit
      exact ⟨by omega, by omega⟩
    · unfold requiredPages
      omega
  have hNo : base.toNat + 48 + need.toNat < 18446744073709551616 := by omega
  have hResultBound : resultLocal < frame.params.length + frame.locals.length := hOrder.2.2.2.2
  obtain ⟨hO1, hO2, hO3, hO4, -⟩ := hOrder
  have hTopValid : frame.validIndex topLocal := by unfold Locals.validIndex; omega
  have hPagesValid : frame.validIndex pagesLocal := by unfold Locals.validIndex; omega
  let prepared := prefixFrame frame topLocal pagesLocal base need
  have hPreparedPages : prepared.get pagesLocal =
      some (.i64 (UInt64.ofNat (requiredPages base need))) := by
    rw [requiredPages_word_of_lt base need hNo]
    apply resultFrame_get_result
    · exact le_trans hO1 (by omega)
    · simpa only [Locals.validIndex, resultFrame_params, resultFrame_locals_length] using hPagesValid
  simp only [program, prepareProgram, List.append_assoc]
  rw [← List.append_assoc]
  refine wpA_append_accessFree (by rfl) ?_
  apply prefixProgram_spec needLocal topLocal pagesLocal module_ env store frame base need hValues
    hNeed (by omega) hTopValid (by omega) hPagesValid hGlobal hNo
  rw [← List.append_nil (ensureProgram _)]
  exact ensureProgram_abort module_ env store prepared pagesLocal (requiredPages base need)
    hMemory32 rfl hPreparedPages (by omega) (by unfold requiredPages; omega) hAbort.1 hAbort.2
    _ _ hTrap

end LeanExe.ProofKit.FixedArrayBump

namespace LeanExe.ProofKit.FixedArrayAllocateNone
open Wasm LeanExe.Runtime LeanExe.ProofKit FixedArraySearch

/-- `program_spec_runs` under `wpA`, for a `top` and free roots that are multiples of 8. -/
theorem program_spec_runsA (aborts : Bool) (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start) (fitProgram : Wasm.Program)
    (base need stride previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes) (hNone : takeFirstFit need nodes = none)
    (hBase : base.toNat ≤ 4294967296) (hNeedBound : need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65535) (hMemory32 : module_.memIs64 = false)
    (hCapBound : store.memoryCap module_ 0 ≤ 65535) (hBaseAl : base.toNat % 8 = 0)
    (hRoots : ∀ node ∈ nodes, node.root.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hTrap : aborts = true → ∀ st, Q (.Trap st "unreachable"))
    (hRoom : aborts = false → base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < FixedArrayBump.requiredPages base need →
        FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0))
    (hNext : base.toNat + 48 + need.toNat ≤ 4294901760 → ∀ previous : UInt64, wpA module_ rest Q
      (counted (FixedArrayBump.allocated store base need stride) count)
      (frame params saved tail need previous 0 (base + 48 + need)
        ((base + 48 + need - 1) / 65536 + 1) (base + 48)) env) :
    wpA module_ (program start fitProgram stride ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  subst start
  simp only [program, List.append_assoc]
  refine wpA_append_accessFree (by rfl) ?_
  rw [← List.append_nil (initializeProgram _)]
  refine initializeProgram_spec module_ env store params saved tail _ rfl need previous current
    capacity next result (freeHead nodes) hGlobal1 _ _ (wp_nil.mpr ?_)
  apply noneProgram_specA module_ env store params saved tail _ rfl fitProgram need capacity next
    nodes hList hNone hRoots
  intro previous oldCapacity oldNext
  simp [wpA_simp, wp_simp, frame, Nat.add_assoc]
  refine wpA_iff_cons rfl ?_
  simp only
  apply FixedArrayBump.program_spec_runsA aborts _ _ _ _ module_ env store
    (frame params saved tail need previous 0 oldCapacity oldNext 0) base need stride rfl
  · simp [frame, Locals.get, Nat.add_assoc]
  · simp [frame, Locals.validIndex, Nat.add_assoc]
  · exact hGlobal0
  · exact hBase
  · exact hNeedBound
  · exact hPages
  · exact hMemory32
  · exact hCapBound
  · exact hBaseAl
  · exact fun h st => hTrap h st
  · exact hRoom
  intro hFit
  rw [← Nat.add_assoc params.length saved.length 3,
    ← Nat.add_assoc params.length saved.length 4,
    ← Nat.add_assoc params.length saved.length 5, bump_result]
  simp only [wpA_nil, List.take_zero, List.drop_zero, List.nil_append, frame]
  refine wpA_append_accessFree (by rfl) ?_
  rw [← List.append_nil countProgram]
  refine countProgram_spec module_ env _ _ count rfl
    ((allocated_count store base need stride).trans hGlobal2) _ _ (wp_nil.mpr ?_)
  exact hNext hFit previous

end LeanExe.ProofKit.FixedArrayAllocateNone

namespace LeanExe.ProofKit.FixedArrayAllocate
open Wasm LeanExe.Runtime LeanExe.ProofKit FixedArraySearch FixedArrayAllocateNone

/-- `program_spec_runs` under `wpA`: for a `top`, free roots and capacities, and a request that
are multiples of 8, every 64-bit access of the allocation is aligned. -/
theorem program_spec_runsA (aborts : Bool) (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (params saved tail : List Wasm.Value) (start : Nat)
    (hStart : params.length + saved.length = start)
    (base need stride previous current capacity next result count : UInt64)
    (nodes : List FreeNode)
    (hGlobal0 : store.globals.globals[0]? = some (.i64 base))
    (hGlobal1 : store.globals.globals[1]? = some (.i64 (freeHead nodes)))
    (hGlobal2 : store.globals.globals[2]? = some (.i64 count))
    (hList : FreeListAt store.mem nodes)
    (hBase : base.toNat ≤ 4294967296) (hNeedBound : need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65535) (hMemory32 : module_.memIs64 = false)
    (hCapBound : store.memoryCap module_ 0 ≤ 65535) (hBaseAl : base.toNat % 8 = 0)
    (hRoots : ∀ node ∈ nodes, node.root.toNat % 8 = 0)
    (hCapacities : ∀ node ∈ nodes, node.capacity.toNat % 8 = 0) (hNeedAl : need.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hTrap : aborts = true → ∀ st, Q (.Trap st "unreachable"))
    (hRoom : aborts = false → takeFirstFitFrom 0 need nodes = none →
      base.toNat + 48 + need.toNat ≤ 4294967296 ∧
      (store.mem.pages < FixedArrayBump.requiredPages base need →
        FixedArrayBump.requiredPages base need ≤ store.memoryCap module_ 0))
    (hNext : (takeFirstFitFrom 0 need nodes = none →
        base.toNat + 48 + need.toNat ≤ 4294901760) →
      ∀ previous current capacity next : UInt64, wpA module_ rest Q
      (counted (allocated store base need stride nodes) count)
      (frame params saved tail need previous current capacity next (root base need nodes)) env) :
    wpA module_ (program start stride ++ rest) Q store
      (frame params saved tail need previous current capacity next result) env := by
  subst start
  cases hTake : takeFirstFitFrom 0 need nodes with
  | none =>
    have hNone : takeFirstFit need nodes = none := by
      rw [← takeFirstFitFrom_project 0 need nodes, hTake]
      rfl
    apply FixedArrayAllocateNone.program_spec_runsA aborts module_ env store params saved tail _
      rfl (FixedArrayReuse.program (params.length + saved.length) stride)
      base need stride previous current capacity next result count nodes
      hGlobal0 hGlobal1 hGlobal2 hList hNone hBase hNeedBound hPages hMemory32 hCapBound hBaseAl
      hRoots Q rest hTrap (fun h => hRoom h hTake)
    intro hFit previous
    simpa only [allocated, root, hTake] using
      hNext (fun _ => hFit) previous 0 (base + 48 + need) ((base + 48 + need - 1) / 65536 + 1)
  | some choice =>
    have hRoot := reuseRoot_ne_zero hList hTake
    simp only [program, FixedArrayAllocateNone.program, List.append_assoc]
    refine wpA_append_accessFree (by rfl) ?_
    rw [← List.append_nil (initializeProgram _)]
    refine initializeProgram_spec module_ env store params saved tail _ rfl need previous current
      capacity next result (freeHead nodes) hGlobal1 _ _ (wp_nil.mpr ?_)
    apply fitProgram_specA module_ env store params saved tail _ rfl need capacity next stride
      nodes choice hGlobal1 hList hTake hRoots hCapacities hNeedAl
    simp [wpA_simp, wp_simp, frame, Nat.add_assoc, hRoot]
    refine wpA_iff_cons rfl ?_
    simp [wpA_simp, wp_simp]
    have hCount : (fixedArrayReuseStore store choice need stride).globals.globals[2]? =
        some (.i64 count) := by
      simpa only [allocated, hTake] using
        (allocated_count store base need stride nodes).trans hGlobal2
    refine wpA_append_accessFree (by rfl) ?_
    rw [← List.append_nil countProgram]
    refine countProgram_spec module_ env _ _ count rfl hCount _ _ (wp_nil.mpr ?_)
    simpa only [allocated, root, hTake, frame, List.cons_append, List.nil_append] using
      hNext (fun h => by simp [hTake] at h) choice.previous choice.node.root choice.node.capacity
        choice.next

end LeanExe.ProofKit.FixedArrayAllocate
