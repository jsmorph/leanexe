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

theorem function_shape : func0 = func0.take 4 ++
    [.block 0 0 [.loop 0 0 loopBody]] ++ func0.drop 5 := rfl

theorem loop_shape : loopBody = loopBody.take 35 ++
    [.iff 0 0 positive negative, .br 0] := rfl

theorem positive_shape : positive = positive.take 14 ++
    PackedPush.program 29 ++ positive.drop 58 := rfl

theorem negative_shape : negative = negative.take 18 ++
    PackedPush.program 29 ++ (negative.drop 62).take 7 ++
    PackedReleaseGuard.program 5 21 5 ++ negative.drop 75 := rfl

theorem release_function : «module».funcs[5]? =
    some { Project.Runtime.releaseFuncDef 5 with typeIdx := some 5 } := rfl

#print axioms function_shape
#print axioms loop_shape
#print axioms positive_shape
#print axioms negative_shape
#print axioms release_function
end Project.LebU32.Recycling
