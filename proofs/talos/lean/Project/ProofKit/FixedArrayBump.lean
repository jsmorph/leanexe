import Project.ProofKit.FixedArrayBumpInstall
import Project.ProofKit.FixedArrayHeaderExec
import Project.ProofKit.MemoryEnsure

namespace Project.ProofKit.FixedArrayBump
open Wasm Project.Clob FixedArrayFold MemoryGrowth

def requiredPages (base need : UInt64) : Nat :=
  (base.toNat + 48 + need.toNat - 1) / 65536 + 1

def program (needLocal topLocal pagesLocal resultLocal : Nat) (stride : UInt64) : Wasm.Program :=
  prefixProgram needLocal topLocal pagesLocal ++ ensureProgram pagesLocal ++
    installProgram resultLocal topLocal ++ FixedArrayHeader.program resultLocal needLocal stride

def result (frame : Locals) (topLocal pagesLocal resultLocal : Nat) (base need : UInt64) : Locals :=
  resultFrame (prefixFrame frame topLocal pagesLocal base need) resultLocal (base + 48)

def allocated (store : Store Unit) (base need stride : UInt64) : Store Unit :=
  fixedArrayAllocBumpStore (ensured store (requiredPages base need)) base need stride

theorem requiredPages_le (base need : UInt64)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296) :
    requiredPages base need ≤ 65536 := by
  unfold requiredPages
  omega

theorem requiredPages_word (base need : UInt64)
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296) :
    UInt64.ofNat (requiredPages base need) = (base + 48 + need - 1) / 65536 + 1 := by
  have hBound := requiredPages_le base need hFit32
  have h64 : requiredPages base need < UInt64.size := by
    change requiredPages base need < 18446744073709551616
    omega
  apply UInt64.toNat.inj
  rw [UInt64.toNat_ofNat_of_lt' h64, Allocation.pagesNeeded_toNat base need hFit32]
  rfl

theorem requiredPages_fit (store : Store Unit) (base need : UInt64) :
    base.toNat + 48 + need.toNat ≤
      (ensured store (requiredPages base need)).mem.pages * 65536 := by
  rw [ensured_pages]
  have hPages := Nat.le_max_right store.mem.pages (requiredPages base need)
  have hTotal : base.toNat + 48 + need.toNat ≤ requiredPages base need * 65536 := by
    unfold requiredPages
    omega
  exact hTotal.trans (Nat.mul_le_mul_right 65536 hPages)

theorem program_spec (needLocal topLocal pagesLocal resultLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (base need stride : UInt64) (hValues : frame.values = [])
    (hNeed : frame.get needLocal = some (.i64 need))
    (hOrder : frame.params.length ≤ needLocal ∧ needLocal < topLocal ∧
      topLocal < pagesLocal ∧ pagesLocal < resultLocal ∧ frame.validIndex resultLocal)
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536) (hMemory32 : module_.memIs64 = false)
    (hCap : requiredPages base need ≤ store.memoryCap module_ 0)
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
  apply prefixProgram_spec needLocal topLocal pagesLocal module_ env store frame base need hValues
    hNeed (by omega) hTopValid (by omega) hPagesValid hGlobal hFit32
  apply ensureProgram_spec module_ env store prepared pagesLocal (requiredPages base need)
    hMemory32 rfl hPreparedPages hPages (requiredPages_le base need hFit32) hCap
  apply installProgram_spec resultLocal topLocal module_ env _ prepared base (base + 48 + need)
    rfl hPreparedTop (by exact le_trans hOrder.1 (by omega)) hPreparedValid
    (by exact le_trans hOrder.1 (by omega))
    (by simpa only [prepared, prefixFrame, Locals.validIndex, resultFrame_params,
      resultFrame_locals_length] using hTopValid) (by omega)
  · unfold ensured
    split <;> exact hGlobal
  apply FixedArrayHeader.program_spec module_ env _ _ resultLocal needLocal base need stride
    rfl hFinalRoot hFinalNeed (by omega)
  · exact le_trans (by omega) (requiredPages_fit store base need)
  · exact hNext

#print axioms requiredPages_word
#print axioms requiredPages_fit
#print axioms program_spec

end Project.ProofKit.FixedArrayBump
