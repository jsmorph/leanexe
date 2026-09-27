import Project.EulerRiemann.InitialAllocationCapacity
import Project.ProofKit.FixedArrayBump

namespace Project.EulerRiemann.Execution
open Wasm Project.ProofKit

def InitialAllocationSite.bumpInstruction : InitialAllocationSite → Option Wasm.Instruction
  | .map => initialGrowBody[40]?
  | .append => initialGrowBody[114]?
  | .extract => initialExtractBody[56]?

def InitialAllocationSite.bumpProgram (site : InitialAllocationSite) : Wasm.Program :=
  match site.bumpInstruction with
  | some (.iff _ _ body _ _ _) => body
  | _ => []

theorem initial_bump_instruction (site : InitialAllocationSite) :
    site.bumpInstruction = some (.iff 0 0 site.bumpProgram []) := by
  cases site <;> rfl

theorem initial_bump_shape (site : InitialAllocationSite) :
    site.bumpProgram = FixedArrayBump.program site.capacityLocal (site.capacityLocal + 3)
      (site.capacityLocal + 4) (site.capacityLocal + 5) 7 := by
  cases site <;> rfl

theorem initial_done_bump_shape : initialDoneBody[56]? = InitialAllocationSite.extract.bumpInstruction := by
  rfl

theorem initial_bump_spec (site : InitialAllocationSite)
    (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (base need : UInt64)
    (hParams : frame.params.length = 5) (hLocals : frame.locals.length = 61)
    (hValues : frame.values = [])
    (hNeed : frame.get site.capacityLocal = some (.i64 need))
    (hGlobal : store.globals.globals[0]? = some (.i64 base))
    (hFit32 : base.toNat + 48 + need.toNat ≤ 4294967296)
    (hPages : store.mem.pages ≤ 65536)
    (hCap : FixedArrayBump.requiredPages base need ≤ store.memoryCap module 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q (FixedArrayBump.allocated store base need 7)
      (FixedArrayBump.result frame (site.capacityLocal + 3) (site.capacityLocal + 4)
        (site.capacityLocal + 5) base need) env) :
    wp module (site.bumpProgram ++ rest) Q store frame env := by
  rw [initial_bump_shape]
  apply FixedArrayBump.program_spec site.capacityLocal (site.capacityLocal + 3)
    (site.capacityLocal + 4) (site.capacityLocal + 5) module env store frame base need 7
    hValues hNeed
  · cases site <;> simp [InitialAllocationSite.capacityLocal, Locals.validIndex, hParams, hLocals]
  · exact hGlobal
  · exact hFit32
  · exact hPages
  · rfl
  · exact hCap
  · exact hNext

#print axioms initial_bump_instruction
#print axioms initial_bump_shape
#print axioms initial_done_bump_shape
#print axioms initial_bump_spec

end Project.EulerRiemann.Execution
