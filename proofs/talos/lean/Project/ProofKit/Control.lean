import CodeLib.Entry
import Interpreter.Wasm.Wp.Call
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit

/-- Start a `TerminatesWith` proof for a definitionally equal function and
introduce the initial local frame under the caller-supplied name. -/
macro "wp_entry" f:term " as " initial:term : tactic =>
  `(tactic|
    apply Wasm.TerminatesWith.of_wp_entry (f := $f) rfl <;> intro $initial:term)

/-- Enter a block-wrapped loop with an explicit invariant and decreasing measure. -/
macro "wp_block_loop" " invariant " inv:term " decreasing " measure:term : tactic =>
  `(tactic|
    apply Wasm.wp_block_cons <;>
    apply Wasm.wp_loop_cons (Inv := $inv) (μ := $measure))

/-- Start a generated function and expose its loop-rule goal. -/
macro "wp_entry_to_loop" fDef:ident " unfolding " f:ident
    " as " initial:ident : tactic => do
  let fDefTerm : Lean.TSyntax `term := ⟨fDef.raw⟩
  let initialTerm : Lean.TSyntax `term := ⟨initial.raw⟩
  `(tactic|
    wp_entry $fDefTerm:term as $initialTerm <;>
    unfold $fDef:ident $f:ident <;>
    wp_run <;>
    apply Wasm.wp_block_cons)

/-- Prove an entry function whose straight-line body calls one function and
returns its result, using a supplied theorem for that call. -/
macro "wp_entry_single_call" fDef:ident " unfolding " f:ident
    " as " initial:term " using " h:term : tactic => do
  let fDefTerm : Lean.TSyntax `term := ⟨fDef.raw⟩
  `(tactic|
    wp_entry $fDefTerm:term as $initial <;>
    unfold $fDef:ident $f:ident <;>
    wp_run <;>
    simp <;>
    apply Wasm.wp_call_tw $h <;>
    rintro st' vs hResult <;>
    subst vs <;>
    wp_run <;>
    simp)

end Project.ProofKit
