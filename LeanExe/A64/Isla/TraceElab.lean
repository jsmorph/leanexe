module

public import Lean
public import LeanExe.A64.Isla.Trace
public meta import LeanExe.A64.Isla.Trace

@[expose] public section

/-!
The elaborator `isla_trace%`, in a module of its own so that it can call `parse` and the derived
`ToExpr` instances of `LeanExe.A64.Isla.Trace` at the meta phase, while the trace's definitions stay
ordinary code for the proofs.
-/

namespace LeanExe.A64.Isla

open Lean Elab Term in
/-- The footprint in the files `PATH.opcode` and `PATH.trace`, read when the term elaborates. -/
elab "isla_trace% " path:str : term => do
  let o ← IO.FS.readFile (path.getString ++ ".opcode")
  let s ← IO.FS.readFile (path.getString ++ ".trace")
  match parse o s with
  | .ok t => return toExpr t
  | .error e => throwError "{path.getString}: {e}"

end LeanExe.A64.Isla
