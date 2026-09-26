import Project.ClobDepth.Heap
import Project.ClobDepth.MissingPrepare
import Project.ClobDepth.FoundAllocPrepare
import Project.ClobDepth.FoundFinish

namespace Project.ClobDepth.AllocationEntry
open Wasm Project.Common Project.Clob Project.ProofKit Project.ClobDepth
  Project.ClobDepth.Model Project.ClobDepth.Representation

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

def missingCapacityProg : Program := Entry.missingAllocPrepareProg.take 18

def foundCapacityProg : Program := Entry.foundAllocPrepareProg.take 22

def finishProg (lengthLocal : Nat) : Program :=
  [.localGet 29, .localSet 18, .localGet 18, .wrapI64,
    .localGet lengthLocal, .store64 0, .constI64 0, .localSet 19]

theorem missing_decomposition :
    Entry.missingProg = Entry.missingFieldsProg ++ missingCapacityProg ++
      FixedArrayAllocate.program 24 2 ++ finishProg 17 ++
      Entry.missingCopyProg ++ Entry.missingStoreProg := by rfl

theorem found_decomposition :
    Entry.foundAllocProg = foundCapacityProg ++ FixedArrayAllocate.program 24 2 ++
      finishProg 16 ++ Entry.foundCopyProg ++ Entry.foundStoreProg := by rfl

theorem missingCapacity_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner ptr price qty : UInt64) (levels : List LevelL) (f4 f5 : UInt64)
    (hLength : levels.length < 4294967296)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (MissingPrepare.prepareFrame owner ptr price qty levels f4 f5) env) :
    wp «module» (missingCapacityProg ++ rest) Q st
      (MissingFields.fieldFrame owner ptr price qty levels f4 f5) env := by
  have hBytes : fixedArrayBytes (levels.length + 1) 2 + 7 < UInt64.size := by
    rw [size_eq]
    unfold fixedArrayBytes
    omega
  have hRound := fixedArrayBytesU_round (levels.length + 1) 2
    (by rw [size_eq]; omega) (by decide) hBytes
  have hLengthU : (UInt64.ofNat levels.length).toNat = levels.length := by u64_omega
  have hLengthOne : UInt64.ofNat levels.length + 1 =
      UInt64.ofNat (levels.length + 1) := by
    apply UInt64.toNat.inj
    rw [toNat_add_one (by rw [hLengthU, size_eq]; omega), hLengthU,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
  have hCapacity :
      (8 + (UInt64.ofNat levels.length + 1) * 2 * 8 + 7) / 8 * 8 =
        fixedArrayBytesU (levels.length + 1) 2 := by
    rw [hLengthOne]
    change (fixedArrayBytesU (levels.length + 1) 2 + 7) / 8 * 8 =
      fixedArrayBytesU (levels.length + 1) 2
    exact hRound
  have hNeedNat : (fixedArrayBytesU (levels.length + 1) 2).toNat =
      fixedArrayBytes (levels.length + 1) 2 :=
    fixedArrayBytesU_toNat (levels.length + 1) 2
      (by rw [size_eq]; omega) (by decide) (by omega)
  have hNeedNotLt : ¬fixedArrayBytesU (levels.length + 1) 2 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hNeedNat]
    change ¬fixedArrayBytes (levels.length + 1) 2 < 8
    unfold fixedArrayBytes
    omega
  simp only [missingCapacityProg, Entry.missingAllocPrepareProg, List.take, List.cons_append,
    List.nil_append]
  simp [MissingFields.fieldFrame]
  rw [hCapacity]
  refine wp_iff_cons rfl ?_
  rw [if_neg hNeedNotLt]
  simpa [wp_simp, MissingPrepare.prepareFrame] using hNext


def foundCapacityFrame (owner source price qty : UInt64) (levels : List LevelL)
    (i : Nat) : Locals :=
  let base := FoundAllocPrepare.allocFrame owner source price qty levels i
  { base with locals := (base.locals.set 21 (.i64 (UInt64.ofNat i))).set 22 (.i64 (UInt64.ofNat i + 1)) }

theorem foundCapacity_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner source price qty : UInt64) (levels : List LevelL) (i : Nat)
    (hLength : levels.length < 4294967296)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (foundCapacityFrame owner source price qty levels i) env) :
    wp «module» (foundCapacityProg ++ rest) Q st
      { FoundPrepare.prepareFrame owner source price qty levels i with
          values := [] } env := by
  have hBytes : fixedArrayBytes levels.length 2 + 7 < UInt64.size := by
    rw [size_eq]
    unfold fixedArrayBytes
    omega
  have hRound := fixedArrayBytesU_round levels.length 2
    (by rw [size_eq]; omega) (by decide) hBytes
  have hCapacity :
      (8 + UInt64.ofNat levels.length * 2 * 8 + 7) / 8 * 8 =
        fixedArrayBytesU levels.length 2 := by
    change (fixedArrayBytesU levels.length 2 + 7) / 8 * 8 =
      fixedArrayBytesU levels.length 2
    exact hRound
  have hNeedNat : (fixedArrayBytesU levels.length 2).toNat =
      fixedArrayBytes levels.length 2 :=
    fixedArrayBytesU_toNat levels.length 2
      (by rw [size_eq]; omega) (by decide) (by omega)
  have hNeedNotLt : ¬fixedArrayBytesU levels.length 2 < 8 := by
    rw [UInt64.lt_iff_toNat_lt, hNeedNat]
    change ¬fixedArrayBytes levels.length 2 < 8
    unfold fixedArrayBytes
    omega
  simp only [foundCapacityProg, Entry.foundAllocPrepareProg, List.take, List.cons_append,
    List.nil_append]
  simp [FoundPrepare.prepareFrame]
  rw [hCapacity]
  refine wp_iff_cons rfl ?_
  rw [if_neg hNeedNotLt]
  simpa [wp_simp, foundCapacityFrame, FoundAllocPrepare.allocFrame] using hNext


theorem finish_spec (env : HostEnv Unit) (store : Store Unit) (base : Locals)
    (root length : UInt64) (index : Nat)
    (hParams : base.params.length = 4) (hLocals : base.locals.length = 26)
    (hValues : base.values = []) (hRoot : base.locals[25]? = some (.i64 root))
    (hIndex : index < 14) (hLength : base.locals[index]? = some (.i64 length))
    (hBound : root.toNat % 4294967296 + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Program)
    (hNext : wp «module» rest Q { store with mem := store.mem.write64 root.toUInt32 length }
      (MissingFinish.finishFrame base root) env) :
    wp «module» (finishProg (index + 4) ++ rest) Q store base env := by
  have hRoot' := getElem_of_some hRoot
  have hLength' := getElem_of_some hLength
  have hIndex30 : index + 4 < 30 := by omega
  have hIndexNe : 14 ≠ index := by omega
  simp only [finishProg, List.cons_append, List.nil_append]
  wp_run_with [hParams, hLocals, hValues, hRoot', hLength', hLength, hIndex, hIndex30, hIndexNe, List.getElem_set]
  rw [if_neg (Nat.not_lt.mpr hBound)]
  simpa only [MissingFinish.finishFrame, toUInt32_eq_ofNat] using hNext

#print axioms missing_decomposition
#print axioms found_decomposition
#print axioms missingCapacity_spec
#print axioms foundCapacity_spec
#print axioms finish_spec
end Project.ClobDepth.AllocationEntry
