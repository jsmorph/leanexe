import Project.ClobMarket.InvalidPrepare
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Invalid `market` free-list search

The prepared free-list head is zero.  The generated search loop exits on its
first condition and preserves the store and local frame.  No free-node header
or payload address enters the proof.
-/

namespace Project.ClobMarket.InvalidSearch

open Wasm Project.Clob Project.ClobMarket

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem invalidSearchProg_empty
    (env : HostEnv Unit) (st : Store Unit) (book : UInt64) (order : OrderL)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q st
      (InvalidPrepare.prepareFrame book order) env) :
    wp Project.ClobMarket.«module» (Entry.invalidSearchProg ++ rest) Q st
      (InvalidPrepare.prepareFrame book order) env := by
  let base := InvalidPrepare.prepareFrame book order
  have hParams : base.params.length = 6 := by
    simp [base, InvalidPrepare.prepareFrame, InvalidPrepare.branchFrame,
      InvalidEntry.invalidFrame]
  have hLocals : base.locals.length = 49 := by
    simp [base, InvalidPrepare.prepareFrame, InvalidPrepare.branchFrame,
      InvalidEntry.invalidFrame]
  have hValues : base.values = [] := by
    simp [base, InvalidPrepare.prepareFrame]
  have hIndex : 45 < base.locals.length := by omega
  have hCurrent : base.locals[45]'hIndex = .i64 0 := by
    apply Option.some.inj
    calc
      some (base.locals[45]'hIndex) = base.locals[45]? :=
        (List.getElem?_eq_getElem hIndex).symm
      _ = some (.i64 0) := by
        simp [base, InvalidPrepare.prepareFrame,
          InvalidPrepare.branchFrame, InvalidEntry.invalidFrame]
  have hFrame : Locals.mk base.params base.locals base.values = base := by
    cases base
    rfl
  simp only [Entry.invalidSearchProg, Entry.invalidProg,
    Entry.outerBranch, func21]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = base)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st' s ⟨rfl, rfl⟩
    simp (config := { maxSteps := 10000000 })
      [wp_simp, hParams, hLocals, hValues, hCurrent]
    change wp Project.ClobMarket.«module» rest Q st'
      (Locals.mk base.params base.locals base.values) env
    rw [hFrame]
    exact hNext

end Project.ClobMarket.InvalidSearch
