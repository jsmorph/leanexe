import Project.ClobDepth.MissingPrepare
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Empty free-list search

The prepared free-list head is zero.  The generated search loop exits at its
first condition and preserves the store and local frame.  Both level-update
branches enter the loop with the head in local 26, so the theorem takes the
frame abstractly.
-/

namespace Project.ClobDepth.MissingSearch

open Wasm Project.ClobDepth Project.ClobDepth.Model

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem missingSearchProg_empty
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (hParams : base.params.length = 4)
    (hLocals : base.locals.length = 26)
    (hValues : base.values = [])
    (hCurrent : base.locals[22]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st base env) :
    wp «module» (Entry.missingSearchProg ++ rest) Q st base env := by
  have hIndex : 22 < base.locals.length := by omega
  have hCurrent' : base.locals[22]'hIndex = .i64 0 := by
    apply Option.some.inj
    calc
      some (base.locals[22]'hIndex) = base.locals[22]? :=
        (List.getElem?_eq_getElem hIndex).symm
      _ = some (.i64 0) := hCurrent
  have hFrame : Locals.mk base.params base.locals [] = base := by
    rw [← hValues]
  simp only [Entry.missingSearchProg, List.cons_append, List.nil_append]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s => st' = st ∧ s = base)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st' s ⟨rfl, rfl⟩
    simp (config := { maxSteps := 10000000 })
      [Entry.missingSearchBodyProg, wp_simp, hParams, hLocals, hValues,
        hCurrent']
    rw [hFrame]
    exact hNext

end Project.ClobDepth.MissingSearch
