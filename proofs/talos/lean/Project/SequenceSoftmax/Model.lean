import Project.Softmax.Model
import Project.ExpNeg.Model

namespace Project.SequenceSoftmax

def maximum (scores : Array UInt64) : UInt64 :=
  scores.foldl (fun a b => Softmax.maximum a b) scores[0]!

def weights (scores : Array UInt64) (m : UInt64) : Array UInt64 :=
  scores.map fun x => ExpNeg.evaluate (Wasm.IEEE64.sub x m)

def total (weights : Array UInt64) : UInt64 :=
  weights.foldl (fun a b => Wasm.IEEE64.add a b) 0

def normalize (weights : Array UInt64) (denominator : UInt64) : Array UInt64 :=
  weights.map fun x => Wasm.IEEE64.div x denominator

def compute (scores : Array UInt64) : Array UInt64 :=
  if scores.isEmpty then #[] else
    let w := weights scores (maximum scores)
    normalize w (total w)

end Project.SequenceSoftmax
