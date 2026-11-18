import Verified.Wasi

/-! Kernel tests of the handle check and the axiom audit of its theorems.  The kernel decides the
check of hand-written commands: it refuses `fd_close` and `path_open` outside a bracket, a `.handle`
argument bound to a word other than 3 or to a pair's component under its `letPair`, a pair's
component that `Command.letPair` binds, and a helper call whose argument for a marked parameter is
not a marked variable, and it accepts a `.handle` argument bound to 3, alone, under one or two
`letPair`s, or in the body of a `Command.letPair`, a helper call with a marked variable, and
a bracket nested in the body of another, whose inner open takes the outer handle.  It accepts an
`fd_read` and a `poll_oneoff` whose handle argument, the descriptor of the iovec call and the handle
field of the read subscription, is a marked variable, and refuses both with an unmarked one.  It
refuses `fd_renumber`, hand-written descriptions of `fd_write`, `fd_close`, and `poll_oneoff` that
declare a descriptor a word, and brackets without the close, with the close of the directory, with a
copied handle, with the handle used after the close, with the branches swapped, with a close inside
the body, with the failed descriptor used in the error continuation, and with a last command that
returns the body's result without the close's errno, pairs it with 0 or with the handle's word, or
swaps the pair's components.  It accepts a bracket whose body returns bytes, whose pairs are `pair`,
and `verified_compile_wasi` compiles a program with such a bracket and a program that opens a file
under the preopened directory after `args`, and refuses one whose body returns `Unit`.  The theorems
of the check, of `withOpen`'s reflection and its runs, of the compiled program, and of the trace
corollary use only `propext`, `Classical.choice`, and `Quot.sound`. -/

namespace HandleCheckTest

open LeanExe.Wasi Verified Verified.Wasi

/-- The bracket shape of `withOpen` with a result of the element `element`, over the helpers
`effectSigs`. -/
def bracket {effectSigs : List EffectSig} {context : List Ty} {element : Elem}
    (args : List (Var context .word)) (path : Var context .bytes)
    (onError : Command [] effectSigs (.elem (.prod .word .word) :: context)
      (.value (.elem element)))
    (body : Command [] effectSigs (.word :: .elem (.prod .word .word) :: context)
      (.value (.elem element))) :
    Command [] effectSigs context (.value (.elem (.prod element .word))) :=
  .bind (.sys Call.pathOpen (.flat 1 false) args [path])
    (.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0))
      (.bind onError (.ret (.mk (.var .here) (.word 0))))
      (.bind (.ret (.proj .here (.snd .here)))
        (.bind body
          (.bind (.sys Call.fdClose (.flat 0 false) [.there .here] [])
            (.ret (.mk (.var (.there .here)) (.var .here)))))))

/-- The context of the brackets below: a flags word, the preopened directory, and a path. -/
abbrev outer : List Ty := [.word, .word, .bytes]

/-- `fd_sync` of a variable. -/
def sync {effectSigs : List EffectSig} {context : List Ty} (handle : Var context .word) :
    Command [] effectSigs context (.value .word) :=
  .sys Call.fdSync (.flat 0 false) [handle] []

/-- A bracket under the preopened directory whose body syncs its handle. -/
def single : Command [] [] outer (.value (.elem (.prod .word .word))) :=
  bracket [.there .here, .here, .here, .here, .here, .here] (.there (.there .here))
    (.ret (.proj .here (.fst .here))) (sync .here)

/-- A bracket whose body opens a second file under the first one's handle and syncs both.  The
outer error continuation returns the open's result, a pair like the inner bracket's. -/
def nested : Command [] [] outer (.value (.elem (.prod (.prod .word .word) .word))) :=
  bracket [.there .here, .here, .here, .here, .here, .here] (.there (.there .here))
    (.ret (.var .here))
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

/-- A `.handle` argument bound to the word 3 under a `letPair` of a pair of a word and bytes,
as the reflector writes an operand in the scope of a `BytesResult`. -/
example : (Command.bind (Command.ret (Expr.letPair (.var .here) (Expr.word 3))) (sync .here) :
    Command [] [] [.pair .word .bytes] (.value .word)).handleCheck [] .plain [false] = true := by
  decide +kernel

/-- A `.handle` argument bound to the word 3 under two `letPair`s, in the scope of two pairs. -/
example : (Command.bind (Command.ret (Expr.letPair (.var .here)
      (Expr.letPair (.var (.there (.there (.there .here)))) (Expr.word 3)))) (sync .here) :
    Command [] [] [.pair .word .bytes, .pair .word .bytes] (.value .word)).handleCheck [] .plain
      [false, false] = true := by
  decide +kernel

/-- A `.handle` argument bound to the word 5 under a `letPair`. -/
example : (Command.bind (Command.ret (Expr.letPair (.var .here) (Expr.word 5))) (sync .here) :
    Command [] [] [.pair .word .bytes] (.value .word)).handleCheck [] .plain [false] = false := by
  decide +kernel

/-- A `.handle` argument bound to the first component of a pair under its `letPair`. -/
example : (Command.bind (Command.ret (Expr.letPair (.var .here) (.var (.there .here))))
    (sync .here) : Command [] [] [.pair .word .bytes] (.value .word)).handleCheck [] .plain
      [false] = false := by
  decide +kernel

/-- A `.handle` argument bound to the word 3 in the body of a `Command.letPair`, which binds the
pair's components unmarked. -/
example : (Command.letPair .here (Command.bind (Command.ret (Expr.word 3)) (sync .here)) :
    Command [] [] [.pair .word .bytes] (.value .word)).handleCheck [] .plain [false] = true := by
  decide +kernel

/-- A `.handle` argument that is the first component of a pair, which `Command.letPair` binds
unmarked. -/
example : (Command.letPair .here (sync (.there .here)) :
    Command [] [] [.pair .word .word] (.value .word)).handleCheck [] .plain [false] =
      false := by
  decide +kernel

/-- `fd_read` of the marked directory. -/
example : (Command.sys (pureSigs := []) (effectSigs := []) Call.fdRead .iovecRead
    [.there .here, .here] [] : Command [] [] outer (.value SysForm.iovecRead.ty)).handleCheck
      [] .plain [false, true, false] = true := by decide +kernel

/-- `fd_read` of an unmarked word. -/
example : (Command.sys (pureSigs := []) (effectSigs := []) Call.fdRead .iovecRead
    [.here, .here] [] : Command [] [] outer (.value SysForm.iovecRead.ty)).handleCheck
      [] .plain [false, true, false] = false := by decide +kernel

/-- A read subscription of the marked directory. -/
example : (Command.sys (pureSigs := []) (effectSigs := []) Call.pollOneoffRead .poll
    [.there .here, .here, .here] [] : Command [] [] outer (.value SysForm.poll.ty)).handleCheck
      [] .plain [false, true, false] = true := by decide +kernel

/-- A read subscription of an unmarked word, whose clock words are the marked directory. -/
example : (Command.sys (pureSigs := []) (effectSigs := []) Call.pollOneoffRead .poll
    [.here, .there .here, .there .here] [] :
    Command [] [] outer (.value SysForm.poll.ty)).handleCheck
      [] .plain [false, true, false] = false := by decide +kernel

/-! Wrong commands, W1 to W12, each refused. -/

/-- The arguments of an open under the preopened directory of `outer`. -/
def openArgs : List (Var outer .word) := [.there .here, .here, .here, .here, .here, .here]

/-- The error continuation that returns the errno. -/
def onErrno : Command [] [] (.elem (.prod .word .word) :: outer) (.value .word) :=
  .ret (.proj .here (.fst .here))

/-- `onErrno` followed by the pair of the errno and 0, as a bracket's error branch. -/
def onErrnoPair :
    Command [] [] (.elem (.prod .word .word) :: outer) (.value (.elem (.prod .word .word))) :=
  .bind onErrno (.ret (.mk (.var .here) (.word 0)))

/-- W1: `fd_renumber` of two marked variables. -/
example : (Command.sys (pureSigs := []) (effectSigs := []) Call.fdRenumber (.flat 0 false)
    [.there .here, .there .here] [] : Command [] [] outer (.value .word)).handleCheck [] .plain
      [false, true, false] = false := by decide +kernel

/-- A hand-written description of `fd_write` whose descriptor is `.word32`. -/
def fakeWrite : Call := { name := "fd_write", params := [.word32, .iovec true, .result32] }

/-- W2: `fakeWrite` with the word 1, which is not one of the generated descriptions. -/
example : (Command.bind (Command.ret (Expr.word 1))
    (Command.sys fakeWrite .iovecWrite [.here] [.there .here]) :
    Command [] [] [.bytes] (.value SysForm.iovecWrite.ty)).handleCheck [] .plain [false] =
      false := by decide +kernel

/-- A hand-written description of `fd_close` whose parameter is `.word32`. -/
def fakeClose : Call := { name := "fd_close", params := [.word32] }

/-- W2b: `fakeClose` with the word 1. -/
example : (Command.bind (Command.ret (Expr.word 1))
    (Command.sys fakeClose (.flat 0 false) [.here] []) :
    Command [] [] [] (.value (SysForm.flat 0 false).ty)).handleCheck [] .plain [] = false := by
  decide +kernel

/-- A hand-written description of `poll_oneoff` whose descriptor field is a word. -/
def fakePoll : Call :=
  { name := "poll_oneoff",
    params :=
      [.subscriptions [[⟨0, 8, .const 1⟩, ⟨8, 1, .const 1⟩, ⟨16, 4, .word⟩]],
        .result32] }

/-- W2c: `fakePoll` with the word 1. -/
example : (Command.bind (Command.ret (Expr.word 1))
    (Command.sys fakePoll .poll [.here] []) :
    Command [] [] [] (.value SysForm.poll.ty)).handleCheck [] .plain [] = false := by
  decide +kernel

/-- W3: a bracket without the close. -/
example : (Command.bind (Command.sys (pureSigs := []) (effectSigs := []) Call.pathOpen
    (.flat 1 false) openArgs [.there (.there .here)])
    (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onErrnoPair
      (Command.bind (Command.ret (.proj .here (.snd .here)))
        (Command.bind (sync .here) (Command.ret (.mk (.var .here) (.word 0)))))) :
    Command [] [] outer (.value (.elem (.prod .word .word)))).handleCheck [] .plain
      [false, true, false] = false := by
  decide +kernel

/-- W4: a bracket whose close takes the preopened directory. -/
example : (Command.bind (Command.sys (pureSigs := []) (effectSigs := []) Call.pathOpen
    (.flat 1 false) openArgs [.there (.there .here)])
    (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onErrnoPair
      (Command.bind (Command.ret (.proj .here (.snd .here)))
        (Command.bind (sync .here)
          (Command.bind (Command.sys Call.fdClose (.flat 0 false)
              [.there (.there (.there (.there .here)))] [])
            (Command.ret (.mk (.var (.there .here)) (.var .here))))))) :
    Command [] [] outer (.value (.elem (.prod .word .word)))).handleCheck [] .plain
      [false, true, false] = false := by
  decide +kernel

/-- W5: a body that copies the handle and syncs the copy. -/
example : (bracket openArgs (.there (.there .here)) onErrno
    (Command.bind (Command.ret (Expr.var .here)) (sync .here))).handleCheck [] .plain
      [false, true, false] = false := by decide +kernel

/-- W6: a bracket that returns its handle, then a sync of the returned word after the close. -/
example : (Command.bind (bracket openArgs (.there (.there .here)) onErrno
    (Command.ret (Expr.var .here)))
    (Command.bind (Command.ret (.proj .here (.fst .here))) (sync .here))).handleCheck [] .plain
      [false, true, false] = false := by decide +kernel

/-- W7: the branches of the errno test swapped. -/
example : (Command.bind (Command.sys (pureSigs := []) (effectSigs := []) Call.pathOpen
    (.flat 1 false) openArgs [.there (.there .here)])
    (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0))
      (Command.bind (Command.ret (.proj .here (.snd .here)))
        (Command.bind (sync .here)
          (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
            (Command.ret (.mk (.var (.there .here)) (.var .here))))))
      onErrnoPair) :
    Command [] [] outer (.value (.elem (.prod .word .word)))).handleCheck [] .plain
      [false, true, false] = false := by
  decide +kernel

/-- W8: `fd_close` of the handle inside the body. -/
example : (bracket openArgs (.there (.there .here)) onErrno
    (Command.sys Call.fdClose (.flat 0 false) [.here] [])).handleCheck [] .plain
      [false, true, false] = false := by decide +kernel

/-- W9: the error continuation passes the failed open's descriptor word to `fd_sync`. -/
example : (bracket (effectSigs := []) openArgs (.there (.there .here))
    (Command.bind (Command.ret (.proj .here (.snd .here))) (sync .here)) (sync .here)).handleCheck
      [] .plain [false, true, false] = false := by decide +kernel

/-- A bracket whose last command returns the body's result without the close's errno. -/
example : (Command.bind (Command.sys (pureSigs := []) (effectSigs := []) Call.pathOpen
    (.flat 1 false) openArgs [.there (.there .here)])
    (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onErrno
      (Command.bind (Command.ret (.proj .here (.snd .here)))
        (Command.bind (sync .here)
          (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
            (Command.ret (Expr.var (.there .here))))))) :
    Command [] [] outer (.value .word)).handleCheck [] .plain [false, true, false] = false := by
  decide +kernel

/-- The bracket under the preopened directory with the error branch `onErrnoPair` and a body that
syncs its handle, with the command `last` after the close. -/
def closedWith
    (last : Command [] [] (.word :: .word :: .word :: .elem (.prod .word .word) :: outer)
      (.value (.elem (.prod .word .word)))) :
    Command [] [] outer (.value (.elem (.prod .word .word))) :=
  .bind (.sys Call.pathOpen (.flat 1 false) openArgs [.there (.there .here)])
    (.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0)) onErrnoPair
      (.bind (.ret (.proj .here (.snd .here)))
        (.bind (sync .here)
          (.bind (.sys Call.fdClose (.flat 0 false) [.there .here] []) last))))

/-- The last command that `reflect` writes: the body's result with the close's errno. -/
example : (closedWith (.ret (.mk (.var (.there .here)) (.var .here)))).handleCheck [] .plain
    [false, true, false] = true := by decide +kernel

/-- W10: the last command pairs the body's result with 0 in place of the close's errno. -/
example : (closedWith (.ret (.mk (.var (.there .here)) (.word 0)))).handleCheck [] .plain
    [false, true, false] = false := by decide +kernel

/-- W11: the last command swaps the components. -/
example : (closedWith (.ret (.mk (.var .here) (.var (.there .here))))).handleCheck [] .plain
    [false, true, false] = false := by decide +kernel

/-- W12: the last command pairs the body's result with the closed handle's word. -/
example : (closedWith (.ret (.mk (.var (.there .here)) (.var (.there (.there .here)))))).handleCheck
    [] .plain [false, true, false] = false := by decide +kernel

/-- A bracket whose body syncs its handle and returns bytes, so that its pairs are `pair`. -/
example : (Command.bind (Command.sys (pureSigs := []) (effectSigs := []) Call.pathOpen
    (.flat 1 false) openArgs [.there (.there .here)])
    (Command.ite (.cmp .ne (.proj .here (.fst .here)) (.word 0))
      (Command.bind (Command.ret .bytesEmpty) (Command.ret (.pair (.var .here) (.word 0))))
      (Command.bind (Command.ret (.proj .here (.snd .here)))
        (Command.bind (Command.bind (sync .here) (Command.ret .bytesEmpty))
          (Command.bind (Command.sys Call.fdClose (.flat 0 false) [.there .here] [])
            (Command.ret (.pair (.var (.there .here)) (.var .here))))))) :
    Command [] [] outer (.value (.pair .bytes .word))).handleCheck [] .plain
      [false, true, false] = true := by
  decide +kernel

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

open LeanExe in
/-- A program whose bracket's body returns bytes, which `reflect` expands with `pair`. -/
def bytesMain : Action UInt64 := do
  let read ← withOpen .preopened 0 bytes![102] 0 1073741823 1073741823 0
    (fun _ => pure Bytes.empty) fun file => do
      let got ← fdRead file 16
      pure got.bytes
  let _ ← writeStdoutSome read.1
  pure read.2

verified_compile_wasi bytesCommand (main := bytesMain) := [bytesMain]

open LeanExe in
/-- A program that opens a file under the preopened directory after `args`, whose `ArgsResult`
stays in scope.  The reflector splits the `ArgsResult` into its components where `args` binds it,
and binds the directory to the literal 3, whose operand names no variable, without `letPair`s. -/
def argsMain : Action UInt64 := do
  let arguments ← args
  let read ← withOpen .preopened 0 bytes![102] 0 1073741823 1073741823 0
    (fun errno => pure errno) fun file => do
      let got ← fdRead file 16
      pure got.errno
  if arguments.errno != 0 then
    pure arguments.errno
  else if read.1 != 0 then
    pure read.1
  else
    pure read.2

verified_compile_wasi argsCommand (main := argsMain) := [argsMain]

open LeanExe in
/-- A program whose bracket's body returns `Unit`, which `verified_compile_wasi` refuses. -/
def unitMain : Action UInt64 := do
  let closed ← withOpen .preopened 0 bytes![102] 0 1073741823 1073741823 0
    (fun _ => pure ()) fun file => do
      let _ ← fdSync file
      pure ()
  pure closed.2

/-- error: verified_compile_wasi: the body of withOpen must return a value, and it returns Unit -/
#guard_msgs in
verified_compile_wasi unitCommand (main := unitMain) := [unitMain]

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
    ``Verified.Expr.isPreopened_denote,
    ``Verified.Wasi.Command.preopened_handles,
    ``Verified.Wasi.Command.handles,
    ``Verified.Wasi.Command.handles_exec,
    ``Verified.Wasi.Command.handles_prefix,
    ``Verified.Wasi.EffectProg.handlesSafe,
    ``Verified.Wasi.EffectProg.bracketRuns,
    ``Verified.Wasi.withOpen_closes,
    ``Verified.Wasi.Reflect.withOpen_rel,
    ``Verified.Wasi.Reflect.withOpen_rel_mk,
    ``Verified.Wasi.Reflect.withOpen_rel_pair,
    ``HandleCheckTest.bytesCommand.bytesMain.related,
    ``HandleCheckTest.bytesCommand.handles,
    ``HandleCheckTest.argsCommand.handles]
  for theoremName in theorems do
    for axiomName in ← collectAxioms theoremName do
      unless permitted.contains axiomName do
        throwError "{theoremName} uses forbidden axiom {axiomName}"
  logInfo m!"handle check axiom check passed for {theorems.size} theorems"

check_handle_axioms
