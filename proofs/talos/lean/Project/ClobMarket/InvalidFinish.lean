import Project.ClobMarket.InvalidBump
import Project.ClobLimit.RunMatchEmptyAlloc

/-!
# Invalid `market` allocation finalization

The final phase increments the allocation counter, writes the empty array
length, and records the new root in the exported result locals.  Its semantic
store is the shared empty stride-four allocation state.  Later proofs inherit
its ownership and frame lemmas without reopening the stores.
-/

namespace Project.ClobMarket.InvalidFinish

open Wasm Project.Common Project.Clob Project.ClobMarket

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

def finishFrame (base : Locals) (g0 : UInt64) : Locals :=
  let bumped := InvalidBump.bumpFrame base g0
  { bumped with
    locals := ((bumped.locals.set 36 (.i64 (g0 + 48))).set 32
      (.i64 (g0 + 48))).set 35 (.i64 (g0 + 48))
    values := [] }

set_option Elab.async false in
theorem invalidFinishProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (g0 g2 : UInt64)
    (hParams : base.params.length = 6)
    (hLocals : base.locals.length = 49)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536)
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q
      (Project.ClobLimit.RunMatchEmptyAlloc.allocStore st g0 g2)
      (finishFrame base g0) env) :
    wp Project.ClobMarket.«module» (Entry.invalidFinishProg ++ rest) Q
      (fixedArrayAllocBumpStore st g0 8 4)
      (InvalidBump.bumpFrame base g0) env := by
  have hg2Bump :
      (fixedArrayAllocBumpStore st g0 8 4).globals.globals[2]? =
        some (.i64 g2) :=
    fixedArrayAllocBumpStore_global_of_ne_zero st g0 8 4 2 (.i64 g2)
      (by decide) hg2
  have hRoot : (g0 + 48).toNat = g0.toNat + 48 :=
    fixedArrayBumpRoot_toNat g0 (by
      have hSize : UInt64.size = 18446744073709551616 := rfl
      rw [hSize]
      omega)
  have hRootBound : ¬
      (fixedArrayAllocBumpStore st g0 8 4).mem.pages * 65536 <
        (g0 + 48).toNat % 4294967296 + 8 := by
    rw [fixedArrayAllocBumpStore_pages, hRoot,
      Nat.mod_eq_of_lt (by omega)]
    omega
  have hRootBound' : ¬
      (fixedArrayAllocBumpStore st g0 8 4).mem.pages * 65536 <
        (g0.toNat + 48) % 4294967296 + 8 := by
    rw [← hRoot]
    exact hRootBound
  simp only [Entry.invalidFinishProg, Entry.invalidProg,
    Entry.outerBranch, func21]
  simp (config := { maxSteps := 10000000 })
    [wp_simp, InvalidBump.bumpFrame, hParams, hLocals, hg2Bump]
  rw [if_neg hRootBound']
  have hTopValue : g0 + 48 + 8 = g0 + 56 := by
    rw [UInt64.add_assoc]
    rw [show (48 : UInt64) + 8 = 56 by decide]
  simpa only [finishFrame, InvalidBump.bumpFrame,
    Project.ClobLimit.RunMatchEmptyAlloc.allocStore,
    emptyFixedArrayMem, fixedArrayMem, fixedArrayAllocBumpStore,
    hRoot, toUInt32_eq_ofNat, hTopValue] using hNext

end Project.ClobMarket.InvalidFinish
