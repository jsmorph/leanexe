import Project.Gpt2QuantizedCached.Model
import Project.ProofKit.ListValidation

namespace Project.Gpt2QuantizedCached.Model
open LeanExe.Models.Gpt2.Quantized

def blockScan (weights : ByteArray) (layers : List Nat) : Id (Option UInt64 × Unit) :=
  Project.ProofKit.ListValidation.scan
    (fun layer => validBlock weights (blocksOffset + layer * blockBytes)) 2 layers

theorem blockScan_eq (weights : ByteArray) (layers : List Nat) :
    blockScan weights layers =
      if layers.all (fun layer => validBlock weights (blocksOffset + layer * blockBytes)) then
        (none, ()) else (some 2, ()) :=
  Project.ProofKit.ListValidation.scan_eq _ _ _

#print axioms blockScan_eq
end Project.Gpt2QuantizedCached.Model
