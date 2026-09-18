import LeanExe.Models.Gpt2.Kernel
import Project.ProofKit.F32Add
import Project.ProofKit.F32Sub
import Project.ProofKit.F32Mul
import Project.ProofKit.PackedSource

namespace Project.Gpt2CachedStep.LayerNorm
open LeanExe.Models.Gpt2

def means (input : ByteArray) (rows : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE rows (rowMean input)

def inverses (input : ByteArray) (rows : Nat) : ByteArray :=
  LeanExe.Packed.generateUInt32LE rows (fun row => rowInvStd input row (word (means input rows) row))

def value (weights input : ByteArray) (scaleOffset biasOffset rows index : Nat) : UInt32 :=
  Wasm.IEEE32.add
    (Wasm.IEEE32.mul
      (Wasm.IEEE32.mul (Wasm.IEEE32.sub (word input index) (word (means input rows) (index / 768)))
        (word (inverses input rows) (index / 768)))
      (word weights (scaleOffset + index % 768)))
    (word weights (biasOffset + index % 768))

theorem layerNorm_eq (weights input : ByteArray) (scaleOffset biasOffset rows : Nat) :
    layerNorm weights input scaleOffset biasOffset rows =
      LeanExe.Packed.generateUInt32LE (rows * 768) (value weights input scaleOffset biasOffset rows) := by
  unfold layerNorm
  dsimp only
  congr 1
  funext index
  simp only [value, means, inverses, Project.ProofKit.F32Sub.sub_eq,
    Project.ProofKit.F32Mul.mul_eq, Project.ProofKit.F32Add.add_eq]

@[simp] theorem means_size (input : ByteArray) (rows : Nat) : (means input rows).size = 4 * rows :=
  Project.ProofKit.PackedSource.generate_size ..

@[simp] theorem inverses_size (input : ByteArray) (rows : Nat) : (inverses input rows).size = 4 * rows :=
  Project.ProofKit.PackedSource.generate_size ..

#print axioms layerNorm_eq

end Project.Gpt2CachedStep.LayerNorm
