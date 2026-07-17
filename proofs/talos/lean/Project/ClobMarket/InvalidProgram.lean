import Project.ClobMarket.InvalidPost

/-!
# Invalid `market` program composition

This theorem composes preparation, empty search, bump allocation, and
finalization under an abstract assertion.  The exported-function proof can
select the invalid branch without carrying its concrete continuation through
each allocator phase.  Concrete result-local normalization remains in a
separate epilogue theorem.
-/

namespace Project.ClobMarket.InvalidProgram

open Wasm Project.Clob Project.ClobMarket

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

set_option Elab.async false in
theorem invalidProg_spec
    (env : HostEnv Unit) (st : Store Unit) (book g0 g2 : UInt64)
    (order : OrderL)
    (hFit32 : g0.toNat + 56 < 4294967296)
    (hFit : g0.toNat + 56 ≤ st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (hg2 : st.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit)
    (hNext : Q (.Fallthrough
      (Project.ClobLimit.RunMatchEmptyAlloc.allocStore st g0 g2)
      (InvalidFinish.finishFrame
        (InvalidPrepare.prepareFrame book order) g0))) :
    wp Project.ClobMarket.«module» Entry.invalidProg Q st
      (InvalidPrepare.branchFrame book order) env := by
  let base := InvalidPrepare.prepareFrame book order
  have hParams : base.params.length = 6 := by
    simp [base, InvalidPrepare.prepareFrame, InvalidPrepare.branchFrame,
      InvalidEntry.invalidFrame]
  have hLocals : base.locals.length = 49 := by
    simp [base, InvalidPrepare.prepareFrame, InvalidPrepare.branchFrame,
      InvalidEntry.invalidFrame]
  have hValues : base.values = [] := by
    simp [base, InvalidPrepare.prepareFrame]
  have hNeed : base.locals[43]? = some (.i64 8) := by
    simp [base, InvalidPrepare.prepareFrame, InvalidPrepare.branchFrame,
      InvalidEntry.invalidFrame]
  have hResult : base.locals[48]? = some (.i64 0) := by
    simp [base, InvalidPrepare.prepareFrame, InvalidPrepare.branchFrame,
      InvalidEntry.invalidFrame]
  rw [Entry.invalidProg_decomposition]
  simp only [List.append_assoc]
  apply InvalidPrepare.invalidPrepareProg_spec env st book order hg1
  apply InvalidSearch.invalidSearchProg_empty env st book order
  apply InvalidBump.invalidBumpProg_spec env st base g0 hParams hLocals
    hValues hNeed hResult hFit32 hFit hPages hg0
  apply InvalidFinish.invalidFinishProg_spec env st base g0 g2 hParams
    hLocals hFit32 hFit hg2
  simpa only [wp_simp] using hNext

end Project.ClobMarket.InvalidProgram
