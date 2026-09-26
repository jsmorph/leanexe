import Project.LebU32.Program
import Project.ProofKit.PackedPush
import Project.ProofKit.PackedReleaseGuard

namespace Project.LebU32.Spec
open Wasm Project.ProofKit

def loopCode : Wasm.Program :=
  match (func0[4]? : Option Wasm.Instruction) with
  | some (.block _ _ [.loop _ _ body _ _] _ _) => body
  | _ => []

def finalByteCode : Wasm.Program :=
  match (loopCode[35]? : Option Wasm.Instruction) with
  | some (.iff _ _ yes _ _ _) => yes
  | _ => []

def continueByteCode : Wasm.Program :=
  match (loopCode[35]? : Option Wasm.Instruction) with
  | some (.iff _ _ _ no _ _) => no
  | _ => []

theorem loop_shape : func0 = func0.take 4 ++ [.block 0 0 [.loop 0 0 loopCode]] ++ func0.drop 5 := rfl

theorem iteration_shape : loopCode = loopCode.take 35 ++ [.iff 0 0 finalByteCode continueByteCode, .br 0] := rfl

theorem final_push_shape : finalByteCode = finalByteCode.take 14 ++
    PackedPush.program 29 ++ finalByteCode.drop 58 := rfl

theorem continue_push_shape : continueByteCode = continueByteCode.take 18 ++
    PackedPush.program 29 ++ continueByteCode.drop 62 := rfl

theorem continue_release_shape : (continueByteCode.drop 69).take 6 =
    PackedReleaseGuard.program 5 21 5 := rfl

#print axioms loop_shape
#print axioms iteration_shape
#print axioms final_push_shape
#print axioms continue_push_shape
#print axioms continue_release_shape
end Project.LebU32.Spec
