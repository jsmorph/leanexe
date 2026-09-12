import Project.EulerRiemann.InitialExtractCopy
import Project.ProofKit.FixedArrayCapacityArithmetic

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit.FixedArrayCapacity

inductive InitialAllocationSite where
  | map
  | append
  | extract

def InitialAllocationSite.lengthLocal : InitialAllocationSite → Nat
  | .map => 49
  | .append => 52
  | .extract => 53

def InitialAllocationSite.capacityLocal : InitialAllocationSite → Nat
  | .map => 54
  | .append => 59
  | .extract => 60

def InitialAllocationSite.capacityProgram : InitialAllocationSite → Wasm.Program
  | .map => (initialGrowBody.drop 12).take 18
  | .append => (initialGrowBody.drop 86).take 18
  | .extract => (initialExtractBody.drop 28).take 18

theorem initial_capacity_shape (site : InitialAllocationSite) :
    site.capacityProgram = localProgram site.lengthLocal 7 site.capacityLocal := by
  cases site <;> rfl

theorem initial_done_capacity_shape : (initialDoneBody.drop 28).take 18 =
    InitialAllocationSite.extract.capacityProgram := by
  rfl

theorem initial_capacity_spec (site : InitialAllocationSite)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (length : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hLength : frame.get site.lengthLocal = some (.i64 length))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q store
      (capacityFrame frame site.capacityLocal (normalizedCapacity length 7)) env) :
    wp module (site.capacityProgram ++ rest) Q store frame env := by
  rw [initial_capacity_shape]
  apply localProgram_spec site.lengthLocal length 7 site.capacityLocal
    module env store frame hLength hValues
  · cases site <;> simp [InitialAllocationSite.capacityLocal, hParams]
  · cases site <;> simp [InitialAllocationSite.capacityLocal, Locals.validIndex, hParams, hLocals]
  · exact hNext

theorem initial_capacity_toNat (length : UInt64) (hLength : length.toNat ≤ 1048576) :
    (normalizedCapacity length 7).toNat = 8 + length.toNat * 56 := by
  have hFit : 8 + length.toNat * (7 : UInt64).toNat * 8 + 7 < UInt64.size := by
    change 8 + length.toNat * 7 * 8 + 7 < 18446744073709551616
    omega
  have hSeven : (7 : UInt64).toNat = 7 := rfl
  simpa only [hSeven, Nat.mul_assoc, Nat.reduceMul] using normalizedCapacity_toNat_of_fits length 7 hFit

#print axioms initial_capacity_shape
#print axioms initial_done_capacity_shape
#print axioms initial_capacity_spec
#print axioms initial_capacity_toNat

end Project.EulerRiemann.Execution
