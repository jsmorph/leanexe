import Demos.OrderBook.ProcessCorrect

/-! The axiom audit of the order book's process: every theorem in the namespace
`Demos.OrderBook.Process`, and the lemmas about `Spec.run` that the process's batch lemma adds, use
only `propext`, `Classical.choice`, and `Quot.sound`. -/

open Lean Elab Command in
elab "check_orderbook_process_axioms" : command => do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let added := [``Demos.OrderBook.Spec.foldl_nextId_le, ``Demos.OrderBook.Spec.run_nextId_le,
    ``Demos.OrderBook.Spec.foldl_events_length, ``Demos.OrderBook.Spec.run_events_length,
    ``Demos.OrderBook.Spec.encodeAll_size]
  let env ← getEnv
  let theorems := env.constants.toList.filterMap fun (name, info) =>
    if (`Demos.OrderBook.Process).isPrefixOf name && info matches .thmInfo _ then some name
    else none
  for declaration in theorems ++ added do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Order book process axiom check passed for {theorems.length + added.length} theorems"

check_orderbook_process_axioms

#print axioms Demos.OrderBook.Process.process_output
#print axioms Demos.OrderBook.Process.process_exec_correct
#print axioms Demos.OrderBook.Process.process_terminates
#print axioms Demos.OrderBook.Process.process_terminates_future
#print axioms Demos.OrderBook.Process.batch_refines
#print axioms Demos.OrderBook.Process.future_step
