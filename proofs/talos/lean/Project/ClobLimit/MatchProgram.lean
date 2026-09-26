import Project.ClobLimit.MatchDispatch
import Project.ClobLimit.MatchLocals
import Project.ClobLimit.SearchRegion
import Project.ClobMatchFuel.LoopGuard

namespace Project.ClobLimit.MatchProgram
open Wasm Project.FunctionRegion

def sourceLoop : Wasm.Program :=
  [.block 0 0 [.loop 0 0
    (Project.ClobMatchFuel.LoopControl.loopGuardProg ++
      MatchDispatch.dispatchProg ++ [.br 0])]]

def loop : Wasm.Program :=
  LocalRegion.renameProgram MatchLocals.rename
    (FunctionRegion.renameProgram SearchRegion.searchRename sourceLoop)

def initProg : Wasm.Program :=
  [.constI64 0, .localSet 11, .constI64 0, .localSet 12,
    .constI64 0, .localSet 18]

def finish : Wasm.Program :=
  [.localGet 18, .constI64 0, .eqI64,
    .iff 0 0
      [.localGet 6, .localSet 13, .localGet 7, .localSet 14,
       .localGet 8, .localSet 15, .localGet 9, .localSet 16,
       .localGet 10, .localSet 17] [],
    .localGet 13, .localGet 14, .localGet 15, .localGet 16, .localGet 17]

set_option maxRecDepth 1048576 in
theorem decomposition : func17 = initProg ++ loop ++ finish := by
  rfl

#print axioms decomposition

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 800000 in
theorem sourceLoop_portable : FunctionRegion.PortableProgram SearchRegion.SearchDomain
    sourceLoop := by
  prove_portable
  all_goals simp [SearchRegion.SearchDomain]

set_option maxRecDepth 1048576 in
theorem sourceLoop_allowed : LocalRegion.AllowsProgram MatchLocals.Domain sourceLoop := by
  decide

end Project.ClobLimit.MatchProgram
