import Project.EulerGridStep.InitializationShape
import Project.EulerGridStep.Helpers

namespace Project.EulerGridStep.Execution
open Wasm
open Project.ProofKit
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000

def gridEntryFrame (ratio pointer : UInt64) : Locals :=
  { params := [.i64 ratio, .i64 pointer], locals := List.replicate 43 (.i64 0), values := [] }

def gridEntryInvalid (ratio : UInt64) (length : Nat) : Bool :=
  !Project.EulerConservative.Model.positiveBits ratio || length == 0 || length % 3 != 0

def gridGuardFrame (ratio pointer : UInt64) (length : Nat) : Locals :=
  let ls := (gridEntryFrame ratio pointer).locals.set 0 (.i64 ratio)
  let ls := if Project.EulerConservative.Model.positiveBits ratio then
    let ls := ls.set 31 (.i64 pointer)
    if length = 0 then ls else ((ls.set 33 (.i64 pointer)).set 31 (.i64 (UInt64.ofNat length))).set 32 (.i64 3)
    else ls
  { params := [.i64 ratio, .i64 pointer], locals := ls,
    values := [.i32 (if gridEntryInvalid ratio length then 1 else 0)] }

/-- Exact ratio/empty/remainder guards, including short-circuit paths and their scratch frame. -/
theorem grid_entry_guards_spec {m : Wasm.Module} (layout : Layout m)
    (env : HostEnv Unit) (initial : Store Unit) (ratio pointer : UInt64) (input : Array UInt64)
    (hInput : UInt64Array.At initial pointer input)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp m rest Q initial (gridGuardFrame ratio pointer input.size) env) :
    wp m (func36.take 17 ++ rest) Q initial (gridEntryFrame ratio pointer) env := by
  have hSize64 := hInput.size_lt
  have hSizeNat := UInt64.toNat_ofNat_of_lt' hSize64
  have hLengthBound := hInput.generatedLengthBound
  have hLengthRead := hInput.lengthRead
  have hPointerAddress := hInput.pointerAddress_eq
  have hZero : UInt64.ofNat input.size = 0 ↔ input.size = 0 := by
    constructor
    · intro h
      simpa only [hSizeNat, UInt64.toNat_zero] using congrArg UInt64.toNat h
    · intro h
      simp [h]
  have hMod : UInt64.ofNat input.size % 3 = UInt64.ofNat (input.size % 3) :=
    (UInt64.ofNat_mod hSize64 (by decide)).symm
  have hRemNat := UInt64.toNat_ofNat_of_lt' (show input.size % 3 < UInt64.size by omega)
  have hRemZero : UInt64.ofNat (input.size % 3) = 0 ↔ input.size % 3 = 0 := by
    constructor
    · intro h
      simpa only [hRemNat, UInt64.toNat_zero] using congrArg UInt64.toNat h
    · intro h
      simp [h]
  wp_run [func36, List.take, gridEntryFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
    List.cons_append, List.nil_append, List.replicate, reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub]
  refine wp_call_tw (Project.EulerConservative.Execution.positiveBits_exact
    layout.toCellLayout.toLayout.toHelperLayout env initial ratio) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  cases hp : Project.EulerConservative.Model.positiveBits ratio <;>
    by_cases hEmpty : input.size = 0 <;> by_cases hRem : input.size % 3 = 0
  all_goals
    repeat first
      | wp_run [gridEntryFrame, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
          Project.EulerConservative.Execution.boolWord, hp, hEmpty, hRem]
      | simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
      | rw [ite_eq_right (Nat.not_lt.mpr hLengthBound)]
      | refine wp_iff_cons rfl ?_
        simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.ofNat_div, -UInt64.ofNat_mod]
    simpa [gridGuardFrame, gridEntryFrame, gridEntryInvalid, hp, hEmpty, hRem] using hNext

#print axioms grid_entry_guards_spec
end Project.EulerGridStep.Execution
