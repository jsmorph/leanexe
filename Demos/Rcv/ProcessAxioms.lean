import Demos.Rcv.ProcessCompiledCorrect

/-! The axiom audit of the tabulator's process, native and compiled, and of the closed form of
`tabulate`'s bound: every theorem in the namespace `Demos.Rcv.Process`, which holds the native
proofs, the generic theorems of `Demos/Rcv/ProcessRun.lean`, the declarations that
`verified_compile_wasi` generates under `io`, the module's theorems, and the charges, and the
theorems of `Demos/Rcv/TabulateBound.lean` and the C call theorem `tabulate_native`, use only
`propext`, `Classical.choice`, and `Quot.sound`.  The full check's build reports the
`#print axioms` lines and fails on the audit's error. -/

open Lean Elab Command in
run_cmd do
  let permitted := #[``propext, ``Classical.choice, ``Quot.sound]
  let added := [``Demos.Rcv.TabulateProgram.tabulate_bound,
    ``Demos.Rcv.TabulateProgram.readContest_bound, ``Demos.Rcv.TabulateProgram.printReport_bound,
    ``Demos.Rcv.TabulateProgram.printError_bound, ``Demos.Rcv.TabulateProgram.count_bound_eq,
    ``Demos.Rcv.TabulateProgram.count_bound_tabulate, ``Demos.Rcv.TabulateProgram.headerText_le,
    ``Demos.Rcv.TabulateProgram.reportFile_length_le,
    ``Demos.Rcv.TabulateProgram.report_length_le, ``Demos.Rcv.TabulateProgram.tabulate_trapFree,
    ``Demos.Rcv.TabulateProgram.tabulate_native, ``Demos.Rcv.TabulateProgram.tabulate_native_size,
    ``Demos.Rcv.TabulateProgram.tabulate_native_8800000, ``Demos.StreamFold.StreamHost.readAll,
    ``Demos.StreamFold.StreamHost.readAll_whole, ``Demos.StreamFold.StreamHost.readAll_long]
  let env ← getEnv
  let theorems := env.constants.toList.filterMap fun (name, info) =>
    if (`Demos.Rcv.Process).isPrefixOf name && info matches .thmInfo _ then some name
    else none
  for declaration in theorems ++ added do
    for axiomName in ← collectAxioms declaration do
      unless permitted.contains axiomName do
        throwError "{declaration} uses forbidden axiom {axiomName}"
  logInfo m!"RCV process axiom check passed for {theorems.length + added.length} theorems"

#print axioms Demos.Rcv.Process.process_output
#print axioms Demos.Rcv.Process.process_exec_correct
#print axioms Demos.Rcv.Process.process_terminates
#print axioms Demos.Rcv.Process.future_step
#print axioms Demos.Rcv.Process.implements
#print axioms Demos.Rcv.Process.run_initial
#print axioms Demos.Rcv.Process.bytes
#print axioms Demos.Rcv.Process.Compiled.target_terminates
#print axioms Demos.Rcv.Process.Compiled.terminates_of_room
#print axioms Demos.Rcv.Process.Compiled.exits_long_of_room
#print axioms Demos.Rcv.Process.step_prefix_bound
#print axioms Demos.Rcv.Process.terminates_of_room
#print axioms Demos.Rcv.Process.initial_terminates
#print axioms Demos.Rcv.Process.initial_exits_long
#print axioms Demos.Rcv.Process.begin_report
#print axioms Demos.Rcv.Process.begin_long
#print axioms Demos.Rcv.Process.begin_prefix_bound
#print axioms Demos.StreamFold.StreamHost.readAll
#print axioms Demos.Rcv.Process.terminates_bytes
#print axioms Demos.Rcv.TabulateProgram.tabulate_bound
#print axioms Demos.Rcv.TabulateProgram.tabulate_native
#print axioms Demos.Rcv.TabulateProgram.tabulate_native_size
#print axioms Demos.Rcv.TabulateProgram.tabulate_native_8800000
