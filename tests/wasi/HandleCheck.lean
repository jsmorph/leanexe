import Verified.Wasi

/-! Kernel tests of the handle check and the axiom audit of its theorems.  The kernel decides the
check of hand-written commands: it refuses `fd_close` and `path_open` outside a bracket, a
`.handle` argument bound to a word other than 3, and a helper call whose argument for a marked
parameter is not a marked variable, and it accepts a `.handle` argument bound to 3, a helper call
with a marked variable, and a bracket nested in the body of another, whose inner open takes the
outer handle.  The theorems of the check, of `withOpen`'s reflection, and of the trace corollary
use only `propext`, `Classical.choice`, and `Quot.sound`. -/

namespace HandleCheckTest

open LeanExe.Wasi Verified Verified.Wasi

/-- The bracket shape of `withOpen` with a result word, over the helpers `effectSigs`. -/
def bracket {effectSigs : List EffectSig} {context : List Ty} (args : List (Var context .word))
    (path : Var context .bytes)
    (onError : Command [] effectSigs (.elem (.prod .word .word) :: context) (.value .word))
    (body : Command [] effectSigs (.word :: .elem (.prod .word .word) :: context) (.value .word)) :
    Command [] effectSigs context (.value .word) :=
  .bind (.sys Call.pathOpen (.flat 1 false) args [path])
    (.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onError
      (.bind (.ret (.proj .here (.snd .here)))
        (.bind body
          (.bind (.sys Call.fdClose (.flat 0 false) [.there .here] [])
            (.ret (.var (.there .here)))))))

/-- The context of the brackets below: a flags word, the preopened directory, and a path. -/
abbrev outer : List Ty := [.word, .word, .bytes]

/-- `fd_sync` of a variable. -/
def sync {effectSigs : List EffectSig} {context : List Ty} (handle : Var context .word) :
    Command [] effectSigs context (.value .word) :=
  .sys Call.fdSync (.flat 0 false) [handle] []

/-- A bracket under the preopened directory whose body syncs its handle. -/
def single : Command [] [] outer (.value .word) :=
  bracket [.there .here, .here, .here, .here, .here, .here] (.there (.there .here))
    (.ret (.proj .here (.fst .here))) (sync .here)

/-- A bracket whose body opens a second file under the first one's handle and syncs both. -/
def nested : Command [] [] outer (.value .word) :=
  bracket [.there .here, .here, .here, .here, .here, .here] (.there (.there .here))
    (.ret (.proj .here (.fst .here)))
    (bracket [.here, .there (.there .here), .there (.there .here), .there (.there .here),
        .there (.there .here), .there (.there .here)] (.there (.there (.there (.there .here))))
      (.ret (.proj .here (.fst .here)))
      (.bind (sync .here) (sync (.there (.there (.there .here))))))

example : single.handleCheck [] .plain [false, true, false] = true := by decide +kernel

example : nested.handleCheck [] .plain [false, true, false] = true := by decide +kernel

/-- The same bracket under an unmarked directory. -/
example : single.handleCheck [] .plain [false, false, false] = false := by decide +kernel

/-- `fd_close` outside a bracket, of a marked variable. -/
example : (Command.sys (pureSigs := []) (effectSigs := []) Call.fdClose (.flat 0 false)
    [.there .here] [] : Command [] [] outer (.value .word)).handleCheck [] .plain
      [false, true, false] = false := by decide +kernel

/-- `path_open` outside a bracket: its result is not tested. -/
example : (Command.bind (Command.sys (pureSigs := []) (effectSigs := []) Call.pathOpen
    (.flat 1 false) [.there .here, .here, .here, .here, .here, .here] [.there (.there .here)])
    (Command.ret (Expr.proj .here (.snd .here))) : Command [] [] outer (.value .word)).handleCheck
      [] .plain [false, true, false] = false := by decide +kernel

/-- A `.handle` argument bound to the word 5. -/
example : (Command.bind (Command.ret (Expr.word 5)) (sync .here) :
    Command [] [] [] (.value .word)).handleCheck [] .plain [] = false := by decide +kernel

/-- A `.handle` argument bound to the word 3, `Handle.preopened`. -/
example : (Command.bind (Command.ret (Expr.word 3)) (sync .here) :
    Command [] [] [] (.value .word)).handleCheck [] .plain [] = true := by decide +kernel

/-- A helper whose parameter is marked. -/
abbrev helper : EffectSig := ⟨"helper", [.word], [.borrowed], .value .word⟩

/-- A call of the helper with a variable of a context. -/
def callHelper {context : List Ty} (handle : Var context .word) :
    Command [] [helper] context (.value .word) :=
  .call .here (Args.cons (.var handle) .nil).get

/-- The helper called with a word bound to 5. -/
example : (Command.bind (Command.ret (Expr.word 5)) (callHelper .here) :
    Command [] [helper] [] (.value .word)).handleCheck [[true]] .plain [] = false := by
  decide +kernel

/-- The helper called with a literal, which is not a variable. -/
example : (Command.call (pureSigs := []) (context := []) EffectVar.here
    (Args.cons (Expr.word 3) .nil).get :
    Command [] [helper] [] (.value .word)).handleCheck [[true]] .plain [] = false := by
  decide +kernel

/-- The helper called with a word bound to 3. -/
example : (Command.bind (Command.ret (Expr.word 3)) (callHelper .here) :
    Command [] [helper] [] (.value .word)).handleCheck [[true]] .plain [] = true := by
  decide +kernel

/-- The helper called with an unmarked variable, when its parameter is not marked. -/
example : (Command.bind (Command.ret (Expr.word 5)) (callHelper .here) :
    Command [] [helper] [] (.value .word)).handleCheck [[false]] .plain [] = true := by
  decide +kernel

end HandleCheckTest

open Lean Elab Command in
elab "check_handle_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let theorems := #[
    ``LeanExe.Wasi.Action.Handles.exec_run,
    ``LeanExe.Wasi.Action.Handles.prefix_run,
    ``LeanExe.Wasi.Action.Handles.bracketRuns,
    ``LeanExe.Wasi.Action.BracketRuns.of_rel,
    ``LeanExe.Wasi.WellBracketed.descriptors,
    ``LeanExe.Wasi.Action.BracketRuns.exec_descriptors,
    ``LeanExe.Wasi.Action.BracketRuns.prefix_descriptors,
    ``Verified.Wasi.Command.handles,
    ``Verified.Wasi.Command.handles_exec,
    ``Verified.Wasi.Command.handles_prefix,
    ``Verified.Wasi.EffectProg.handlesSafe,
    ``Verified.Wasi.EffectProg.bracketRuns,
    ``Verified.Wasi.Reflect.withOpen_rel,
    ``Verified.Wasi.Reflect.withOpen_rel_unit]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"handle check axiom check passed for {theorems.size} theorems"

check_handle_axioms
