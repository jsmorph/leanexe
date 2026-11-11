import Demos.Rcv.Maine.ProcessCompiledCorrect

/-! The axiom audit of the Maine process, native and compiled, and of the Maine module's C call
theorems: every theorem in the namespace `Demos.Rcv.Maine.Process`, which holds the Maine
process's lemmas, the declarations that `verified_compile_wasi` generates under `io`, the module's
theorems, and the charges, and the theorems of `Demos/Rcv/Maine/TabulateBound.lean` and the C call
theorem `tabulate_native`, use only `propext`, `Classical.choice`, and `Quot.sound`.  The generic
theorems of `Demos/Rcv/ProcessRun.lean` that the Maine process instantiates are audited with the
Oakland process in `Demos/Rcv/ProcessAxioms.lean`.  The full check's build reports the
`#print axioms` lines and fails on the audit's error. -/

open Lean Elab Command in
run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let added := [``Demos.Rcv.Maine.TabulateProgram.tabulate_bound,
    ``Demos.Rcv.Maine.TabulateProgram.count_bound,
    ``Demos.Rcv.Maine.TabulateProgram.reportFile_length_le,
    ``Demos.Rcv.Maine.TabulateProgram.tabulate_trapFree,
    ``Demos.Rcv.Maine.TabulateProgram.tabulate_native,
    ``Demos.Rcv.Maine.TabulateProgram.tabulate_native_size,
    ``Demos.Rcv.Maine.TabulateProgram.tabulate_native_8800000]
  let env ← getEnv
  let theorems := env.constants.toList.filterMap fun (name, info) =>
    if (`Demos.Rcv.Maine.Process).isPrefixOf name && info matches .thmInfo _ then some name
    else none
  for declaration in theorems ++ added do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"Maine process axiom check passed for {theorems.length + added.length} theorems"

#print axioms Demos.Rcv.Maine.Process.process_output
#print axioms Demos.Rcv.Maine.Process.begin_report
#print axioms Demos.Rcv.Maine.Process.begin_long
#print axioms Demos.Rcv.Maine.Process.implements
#print axioms Demos.Rcv.Maine.Process.run_initial
#print axioms Demos.Rcv.Maine.Process.bytes
#print axioms Demos.Rcv.Maine.Process.begin_prefix_bound
#print axioms Demos.Rcv.Maine.Process.step_prefix_bound
#print axioms Demos.Rcv.Maine.Process.beginCharge_eq
#print axioms Demos.Rcv.Maine.Process.terminates_of_room
#print axioms Demos.Rcv.Maine.Process.exits_long_of_room
#print axioms Demos.Rcv.Maine.Process.processMemory_le
#print axioms Demos.Rcv.Maine.Process.initial_terminates
#print axioms Demos.Rcv.Maine.Process.initial_exits_long
#print axioms Demos.Rcv.Maine.Process.terminates_bytes
#print axioms Demos.Rcv.Maine.TabulateProgram.tabulate_bound
#print axioms Demos.Rcv.Maine.TabulateProgram.reportFile_length_le
#print axioms Demos.Rcv.Maine.TabulateProgram.tabulate_native
#print axioms Demos.Rcv.Maine.TabulateProgram.tabulate_native_size
#print axioms Demos.Rcv.Maine.TabulateProgram.tabulate_native_8800000
