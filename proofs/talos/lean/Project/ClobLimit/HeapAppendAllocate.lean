import Project.ClobLimit.HeapAppendProgram
import Project.ClobLimit.LimitResidualPrepare
import Project.ClobLimit.HeapResidualFacts
import Project.ProofKit.FixedArraySearchWindow

namespace Project.ClobLimit.HeapAppendAllocate
open Wasm Project.Common Project.Runtime Project.ProofKit Project.ClobLimit
open Project.ClobMatchFuel.LoopInvariant
open Project.ClobLimit.LimitResidualPrepare

def need (ctx : Context) : UInt64 :=
  FixedArrayCapacity.normalizedCapacity (UInt64.ofNat (ctx.result.book.length + 1)) 5

def resultFrame (base : Locals) (ctx : Context) (previous current capacity next root : UInt64) : Locals :=
  FixedArraySearch.frame base.params (base.locals.take 49) [] (need ctx)
    previous current capacity next root

set_option maxRecDepth 1048576

private theorem prepared_eq (base : Locals) (order : Project.Clob.OrderL) (ctx : Context)
    (data : HeapRunMatch.OutputData) (hOrder : OrderLocalsAt base order ctx data) :
    FixedArrayCapacity.capacityFrame base 55 (need ctx) = resultFrame base ctx 0 0 0 0 0 := by
  have hp := hOrder.fields.params
  have hl := hOrder.fields.locals
  have hs := hOrder.fields.scratch
  have hScratch (i : Nat) (hi : 49 ≤ i) (hj : i < 55) :
      base.locals[i]'(by omega) = .i64 0 := getElem_of_some (hs i hi hj)
  have hFrame := FixedArraySearch.frame_eq_of_gets
    (FixedArrayCapacity.capacityFrame base 55 (need ctx)) 49 (need ctx) 0 0 0 0 0
    (by simp [FixedArrayCapacity.capacityFrame, hl]) rfl (by
      intro i hi
      interval_cases i <;>
        simp [FixedArrayCapacity.capacityFrame, Locals.get, hp, hl, hScratch])
  have hTake : (base.locals.take 49).set 49 (.i64 (need ctx)) = base.locals.take 49 :=
    List.set_eq_of_length_le (by simp [hl])
  have hDrop : (base.locals.set 49 (.i64 (need ctx))).drop 55 = [] :=
    List.drop_eq_nil_of_le (by simp [hl])
  simpa [resultFrame, FixedArrayCapacity.capacityFrame, hp, hl,
    List.take_set, hTake, hDrop] using hFrame

/-- Execute the generated capacity arithmetic and first-fit-or-bump allocation. -/
theorem spec (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (order : Project.Clob.OrderL) (ctx : Context) (data : HeapRunMatch.OutputData)
    (hOrder : OrderLocalsAt base order ctx data)
    (hOutput : HeapRunMatch.OutputAt ctx st data)
    (hGeometry : HeapResidualFacts.Geometry ctx st data.toOutputData)
    (hBump : takeFirstFitFrom 0 (need ctx) data.nodes = none →
      data.g0.toNat + 48 + (need ctx).toNat ≤ 4294967296 ∧
      data.g0.toNat + 48 + (need ctx).toNat ≤ st.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : ∀ previous current capacity next,
      wp «module» rest Q
        (FixedArrayAllocateNone.counted
          (FixedArrayAllocate.allocated st data.g0 (need ctx) 5 data.nodes) ctx.expectedG2)
        (resultFrame base ctx previous current capacity next
          (FixedArrayAllocate.root data.g0 (need ctx) data.nodes)) env) :
    wp «module» (FixedArrayCapacity.localProgram 45 5 55 ++
      FixedArrayAllocate.program 55 5 ++ rest) Q st base env := by
  have hp := hOrder.fields.params
  have hl := hOrder.fields.locals
  rw [List.append_assoc]
  apply FixedArrayCapacity.localProgram_spec 45
    (UInt64.ofNat (ctx.result.book.length + 1)) 5 55 «module» env st base
    (by simpa [Locals.get, hp, hl] using hOrder.appendLength)
    hOrder.fields.values (by omega) (by simp [Locals.validIndex, hp, hl])
  change wp «module» _ Q st (FixedArrayCapacity.capacityFrame base 55 (need ctx)) env
  rw [prepared_eq base order ctx data hOrder]
  apply FixedArrayAllocate.program_in_memory «module» env st base.params
    (base.locals.take 49) [] 55 (by simp [hp, hl]) data.g0 (need ctx) 5 0 0 0 0 0
    ctx.expectedG2 data.nodes hOutput.global0 hOutput.global1 hOutput.global2
    hOutput.freeList hBump hGeometry.pageLimit rfl Q rest
  exact hNext

#print axioms spec
end Project.ClobLimit.HeapAppendAllocate
