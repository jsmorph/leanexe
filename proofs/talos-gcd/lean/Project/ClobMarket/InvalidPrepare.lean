import Project.ClobMarket.InvalidEntry

/-!
# Invalid `market` allocation preparation

The invalid branch obtains status one and prepares an empty stride-four fixed
array allocation.  The free-list head is zero, so the following search exits
without inspecting memory.  The theorem records each allocator scratch local
needed by the search and bump phases.
-/

namespace Project.ClobMarket.InvalidPrepare

open Wasm Project.Clob Project.ClobMarket

def branchFrame (book : UInt64) (order : OrderL) : Locals :=
  { InvalidEntry.invalidFrame book order with values := [] }

def prepareFrame (book : UInt64) (order : OrderL) : Locals :=
  { branchFrame book order with
    locals := (((((((branchFrame book order).locals.set 31
      (.i64 1)).set 33 (.i64 1)).set 34 (.i64 book)).set 43
      (.i64 8)).set 48 (.i64 0)).set 44 (.i64 0)).set 45 (.i64 0)
    values := [] }

set_option maxRecDepth 1048576

set_option Elab.async false in
theorem invalidPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit) (book : UInt64) (order : OrderL)
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp Project.ClobMarket.«module» rest Q st
      (prepareFrame book order) env) :
    wp Project.ClobMarket.«module» (Entry.invalidPrepareProg ++ rest) Q st
      (branchFrame book order) env := by
  simp only [Entry.invalidPrepareProg, Entry.invalidProg,
    Entry.outerBranch, func21]
  refine wp_call_tw (Helpers.func20_spec env st) ?_
  rintro st1 values ⟨rfl, rfl⟩
  wp_run
  simp
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run
  simp only [hg1]
  simpa [prepareFrame, branchFrame, InvalidEntry.invalidFrame] using hNext

end Project.ClobMarket.InvalidPrepare
