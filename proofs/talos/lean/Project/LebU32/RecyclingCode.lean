import Project.LebU32.Defs
import Project.ProofKit.Annotation
import Project.ProofKit.PackedPush
import Project.ProofKit.PackedReleaseGuard

namespace Project.LebU32.Recycling
open Wasm Project.ProofKit

def loopBody : Wasm.Program :=
  (Annotation.resolve func0 [⟨4, .block⟩, ⟨0, .loop⟩]).getD []
def positive : Wasm.Program :=
  (Annotation.resolve loopBody [⟨35, .thenBranch⟩]).getD []
def negative : Wasm.Program :=
  (Annotation.resolve loopBody [⟨35, .elseBranch⟩]).getD []

def positiveHead : Wasm.Program :=
  [.localGet 10, .constI64 255, .andI64, .localSet 12, .localGet 3, .localSet 13, .localGet 4, .localSet 14, .localGet 13, .localSet 29, .localGet 14, .localSet 30, .localGet 12, .localSet 31]

def positiveTail : Wasm.Program :=
  [.localSet 15, .localGet 15, .localSet 6, .localGet 15, .localSet 7, .localGet 14, .constI64 1, .addI64, .localSet 8, .constI64 1, .localSet 9]

def negativeHead : Wasm.Program :=
  [.localGet 11, .localSet 16, .localGet 10, .constI64 128, .addI64, .constI64 255, .andI64, .localSet 17, .localGet 3, .localSet 18, .localGet 4, .localSet 19, .localGet 18, .localSet 29, .localGet 19, .localSet 30, .localGet 17, .localSet 31]

def negativeAfterPush : Wasm.Program :=
  [.localSet 21, .localGet 21, .localSet 22, .localGet 19, .constI64 1, .addI64, .localSet 23]

def negativeTail : Wasm.Program :=
  [.localGet 16, .localSet 24, .localGet 21, .localSet 25, .localGet 22, .localSet 26, .localGet 23, .localSet 27, .localGet 21, .localSet 28, .localGet 24, .localSet 1, .localGet 25, .localSet 2, .localGet 26, .localSet 3, .localGet 27, .localSet 4, .localGet 28, .localSet 5, .localGet 0, .constI64 1, .subI64, .localSet 0]

def activeHead : Wasm.Program :=
  [.localGet 0, .constI64 0, .eqI64, .eqz, .iff 0 1 [
     .localGet 9,
     .constI64 0,
     .eqI64
    ] [
     .const 0
    ] [] [.i32], .eqz, .br_if 1, .localGet 1, .localSet 29, .constI64 128, .localSet 30, .localGet 30, .constI64 0, .eqI64, .iff 0 1 [
     .localGet 29
    ] [
     .localGet 29,
     .localGet 30,
     .remUI64
    ] [] [.i64], .localSet 10, .localGet 1, .localSet 29, .constI64 128, .localSet 30, .localGet 30, .constI64 0, .eqI64, .iff 0 1 [
     .constI64 0
    ] [
     .localGet 29,
     .localGet 30,
     .divUI64
    ] [] [.i64], .localSet 11]

def dispatchHead : Wasm.Program :=
  [.localGet 11, .constI64 0, .eqI64, .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64], .constI64 1, .eqI64, .iff 0 1 [
     .constI64 1
    ] [
     .constI64 0
    ] [] [.i64], .constI64 0, .eqI64, .eqz]

theorem function_shape : func0 = func0.take 4 ++
    [.block 0 0 [.loop 0 0 loopBody]] ++ func0.drop 5 := rfl

theorem loop_shape : loopBody = loopBody.take 35 ++
    [.iff 0 0 positive negative, .br 0] := rfl

theorem active_head_shape : loopBody = activeHead ++ loopBody.drop 25 := rfl

theorem dispatch_shape : loopBody.drop 25 = dispatchHead ++ [.iff 0 0 positive negative, .br 0] := rfl

theorem positive_shape : positive = positiveHead ++
    PackedPush.program 29 ++ positiveTail := rfl

theorem negative_shape : negative = negativeHead ++
    PackedPush.program 29 ++ negativeAfterPush ++
    PackedReleaseGuard.program 5 21 5 ++ negativeTail := rfl

theorem release_function : «module».funcs[5]? =
    some { Project.Runtime.releaseFuncDef 5 with typeIdx := some 5 } := rfl

#print axioms function_shape
#print axioms loop_shape
#print axioms positive_shape
#print axioms negative_shape
#print axioms release_function
end Project.LebU32.Recycling
