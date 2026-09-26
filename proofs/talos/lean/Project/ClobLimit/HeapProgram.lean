import Project.ClobLimit.SearchRegion
import Project.ClobMatchFuel.Iteration
import Project.LocalRegion.Exec
import Project.LocalRegion.Build

/-! The internal matcher reuses the exported matcher's allocation and cleanup
branches under a checked local-frame renaming. Owner results occupy two
additional live slots in the internal function. -/
namespace Project.ClobLimit.HeapProgram
open Wasm Project.LocalRegion Project.FunctionRegion
set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

def slots (i : Nat) : Nat :=
  if i = 0 then 0 else if i ≤ 20 then i - 8 else
  if i = 21 then 14 else if i = 73 then 13 else if i = 75 then 15 else i - 6

def Domain (i : Nat) : Prop := i = 0 ∨ 9 ≤ i ∧ i < 95

def layout : Layout slots Domain where
  sourceParams := 9
  sourceLocals := 86
  targetParams := 11
  targetLocals := 78
  sourceBound := by intro i hi; simp only [Domain] at hi; omega
  targetBound := by
    intro i hi
    simp only [Domain] at hi
    simp only [slots]
    split_ifs <;> omega
  injective := by
    intro i j hi hj h
    simp only [Domain] at hi hj
    simp only [slots] at h
    split_ifs at h <;> omega

def rename (p : Program) : Program :=
  LocalRegion.renameProgram SearchRegion.searchRename slots p

def fullProg : Program := rename ClobMatchFuel.Iteration.fullBranchProg

def partialProg : Program := rename ClobMatchFuel.PartialBranch.partialBranchProg

def readProg : Program := rename ClobMatchFuel.SelectedMaker.readProg

def guardProg : Program := rename ClobMatchFuel.LoopControl.loopGuardProg

def stopProg : Program := [
  .localGet 6,
  .localSet 13,
  .localGet 7,
  .localSet 14,
  .localGet 8,
  .localSet 15,
  .localGet 9,
  .localSet 16,
  .localGet 10,
  .localSet 17,
  .constI64 1,
  .localSet 18
]

def searchProg : Program := [
  .localGet 6,
  .localSet 19,
  .localGet 7,
  .localSet 20,
  .localGet 1,
  .localSet 21,
  .localGet 2,
  .localSet 22,
  .localGet 3,
  .localSet 23,
  .localGet 4,
  .localSet 24,
  .localGet 5,
  .localSet 25,
  .localGet 19,
  .localGet 20,
  .localGet 21,
  .localGet 22,
  .localGet 23,
  .localGet 24,
  .localGet 25,
  .call 14,
  .localSet 27,
  .localSet 26,
  .localGet 26,
  .constI64 0,
  .eqI64
]

def dispatchProg : Program :=
  [.localGet 10,
   .constI64 0,
   .eqI64,
   .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64],
   .constI64 1,
   .eqI64,
   .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64],
   .constI64 0,
   .eqI64,
   .eqz,
   .iff 0 0 stopProg
     (searchProg ++ [.iff 0 0 stopProg
       (readProg ++ [.localGet 32, .localGet 10, .leUI64,
         .iff 0 0 fullProg partialProg])])]

def loopProg : Program :=
  [.block 0 0 [.loop 0 0 (guardProg ++ dispatchProg ++ [.br 0])]]

def initProg : Program := [
  .constI64 0,
  .localSet 11,
  .constI64 0,
  .localSet 12,
  .constI64 0,
  .localSet 18
]

def resultProg : Program := [
  .localGet 18,
  .constI64 0,
  .eqI64,
  .iff 0 0 [
   .localGet 6,
   .localSet 13,
   .localGet 7,
   .localSet 14,
   .localGet 8,
   .localSet 15,
   .localGet 9,
   .localSet 16,
   .localGet 10,
   .localSet 17
  ] [],
  .localGet 13,
  .localGet 14,
  .localGet 15,
  .localGet 16,
  .localGet 17
]

theorem decomposition : func17 = initProg ++ loopProg ++ resultProg := by
  rfl

theorem full_portable : PortableProgram SearchRegion.SearchDomain
    ClobMatchFuel.Iteration.fullBranchProg := by
  prove_portable
  all_goals simp [SearchRegion.SearchDomain]

theorem partial_portable : PortableProgram SearchRegion.SearchDomain
    ClobMatchFuel.PartialBranch.partialBranchProg := by
  prove_portable
  all_goals simp [SearchRegion.SearchDomain]

theorem full_allowed : AllowedProgram Domain ClobMatchFuel.Iteration.fullBranchProg := by
  repeat' (first | exact True.intro | apply And.intro)
  all_goals simp [AllowedInstruction, Domain]

theorem partial_allowed : AllowedProgram Domain ClobMatchFuel.PartialBranch.partialBranchProg := by
  repeat' (first | exact True.intro | apply And.intro)
  all_goals simp [AllowedInstruction, Domain]

#print axioms decomposition
#print axioms layout
end Project.ClobLimit.HeapProgram
