import Project.EulerGridStep.FillLoop
import Project.EulerGridStep.HeaderMemory
import Project.ProofKit.FixedArrayResult

namespace Project.ProofKit.UInt64Array

open Wasm Project.EulerGridStep.Execution

def replicateProgram (targetLocal countLocal counterLocal valueLocal : Nat) : Wasm.Program :=
  FixedArrayResult.lengthStoreLocalProgram targetLocal countLocal ++
    fillProgram targetLocal countLocal counterLocal valueLocal

theorem replicate_spec (targetLocal countLocal counterLocal valueLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (target value : UInt64) (count : Nat)
    (counterValid : frame.validIndex counterLocal)
    (targetDifferent : targetLocal ≠ counterLocal) (countDifferent : countLocal ≠ counterLocal)
    (valueDifferent : valueLocal ≠ counterLocal) (values : frame.values = [])
    (targetRead : frame.get targetLocal = some (.i64 target))
    (countRead : frame.get countLocal = some (.i64 count.toUInt64))
    (valueRead : frame.get valueLocal = some (.i64 value))
    (addressBound : target.toNat + 8 * (count + 1) ≤ 4294967296)
    (memoryBound : target.toNat + 8 * (count + 1) ≤ initial.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final, Memory.WritesRange initial final target.toNat (target.toNat + 8 * (count + 1)) →
      At final target (Array.replicate count value) →
      wp module_ rest Q final (FixedArrayCopy.counterFrame frame counterLocal count counterValid) env) :
    wp module_ (replicateProgram targetLocal countLocal counterLocal valueLocal ++ rest) Q initial frame env := by
  have targetNat : target.toUInt32.toNat = target.toNat := by
    rw [Memory.toUInt32_toNat, Nat.mod_eq_of_lt (by omega)]
  have headerWrites : Memory.WritesRange initial (writeLength initial target count) target.toNat
      (target.toNat + 8 * (count + 1)) := by
    apply Memory.WritesRange.write64 <;> rw [targetNat] <;> omega
  rw [replicateProgram, List.append_assoc]
  apply FixedArrayResult.lengthStoreLocal_spec module_ env initial frame target count.toUInt64 targetLocal countLocal
    targetRead countRead (by rw [targetNat]; omega)
  apply fill_loop_spec targetLocal countLocal counterLocal valueLocal module_ env (writeLength initial target count) frame
    target value (payloadSnapshot initial target count) counterValid targetDifferent countDifferent valueDifferent values
    targetRead (by simpa only [payloadSnapshot, Array.size_ofFn] using countRead) valueRead
    (writeLength_array initial target count addressBound memoryBound)
  intro final result filled
  have written : Memory.WritesRange (writeLength initial target count) final target.toNat
      (target.toNat + 8 * (count + 1)) := by
    refine ⟨congrArg (fun store : Store Unit => {store with mem := final.mem}) filled.frame, filled.pages, ?_⟩
    intro address outside
    exact filled.outside address (by simpa only [payloadSnapshot, Array.size_ofFn] using outside.imp (by omega) id)
  have represented := filled.arrayAt
  rw [filled.complete] at represented
  simpa only [payloadSnapshot, Array.size_ofFn] using next final (headerWrites.trans written)
    (by simpa only [payloadSnapshot, Array.size_ofFn] using represented)

#print axioms replicate_spec

end Project.ProofKit.UInt64Array
