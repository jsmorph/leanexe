import Project.ClobMarket.InvalidProgram

/-!
# Invalid `market` public result

The invalid allocator records status one, the borrowed book, and the empty
trade-array root in three locals.  The generated epilogue reads those locals
into the public result stack.  This theorem keeps concrete frame normalization
outside the exported-function proof.
-/

namespace Project.ClobMarket.InvalidResult

open Wasm Project.Clob Project.ClobMarket

def resultFrame (book : UInt64) (order : OrderL) (g0 : UInt64) : Locals :=
  InvalidFinish.finishFrame (InvalidPrepare.prepareFrame book order) g0

def outputFrame (book : UInt64) (order : OrderL) (g0 : UInt64) : Locals :=
  { resultFrame book order g0 with
    values := [.i64 (g0 + 48), .i64 book, .i64 1] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem resultProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (book : UInt64) (order : OrderL) (g0 : UInt64)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q st
      (outputFrame book order g0) env) :
    wp Project.ClobMarket.«module» (Entry.resultProg ++ rest) Q st
      (resultFrame book order g0) env := by
  simp only [Entry.resultProg, List.cons_append, List.nil_append]
  wp_run
  simpa [resultFrame, outputFrame, InvalidFinish.finishFrame,
    InvalidBump.bumpFrame, InvalidPrepare.prepareFrame,
    InvalidPrepare.branchFrame, InvalidEntry.invalidFrame] using hNext

end Project.ClobMarket.InvalidResult
