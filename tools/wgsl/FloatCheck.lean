import Project.WGSL.GptFloatArtifact
import Project.TinyGpt2.FloatSpec.ContractTests
import Project.TinyGpt2.FloatSpec.Evaluation
import Lean

open Project.TinyGpt2 Project.WGSL

#print axioms FloatSpec.Correspondence.hidden_eq
#print axioms FloatSpec.Correspondence.logits_eq
#print axioms FloatSpec.Evaluation.hidden_eq
#print axioms GptFloatArtifact.hidden_interface
#print axioms GptFloatArtifact.finish_interface
#print axioms GptFloatArtifact.hidden_artifact
#print axioms GptFloatArtifact.artifact
#print axioms FloatSpec.ContractTests.negative_zero
#print axioms FloatSpec.ContractTests.head_zero_sign
#print axioms FloatSpec.ContractTests.head_subnormals
#print axioms FloatSpec.ContractTests.balanced_order
#print axioms FloatSpec.ContractTests.sequential_differs
#print axioms FloatSpec.ContractTests.exponential_cutoff
#print axioms FloatSpec.ContractTests.canonical_nan

/-- The executable harness retains the existing cap of four, expressed as a
word comparison. The universal artifact theorem itself has no weight cap. -/
def readWeights (path : String) : IO (Array UInt64) := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size = 2488*8 do throw (IO.userError "expected 2488 binary64 parameter words")
  let mut words := #[]
  for i in [:2488] do
    let mut word : UInt64 := 0
    for j in [:8] do word := word ||| (bytes[i*8+j]!.toUInt64 <<< (8*j).toUInt64)
    unless word &&& 0x7FFFFFFFFFFFFFFF ≤ 0x4010000000000000 do
      throw (IO.userError "parameter word outside finite magnitude-at-most-four domain")
    words := words.push word
  return words

def readIndex (n : Nat) (text : String) : IO (Fin n) := do
  let some value := text.toNat? | throw (IO.userError "invalid unsigned index")
  if h : value < n then return ⟨value,h⟩ else throw (IO.userError "index outside specified domain")

def main (args : List String) : IO Unit := do
  match args with
  | ["--check", hiddenPath, finishPath, weightsPath] =>
      unless (← IO.FS.readBinFile hiddenPath) == Project.TinyGpt2Hidden.Artifact.artifactBytes do
        throw (IO.userError "hidden Wasm bytes differ from the proved artifact")
      unless (← IO.FS.readBinFile finishPath) == FinishBinary.bytes do
        throw (IO.userError "finish Wasm bytes differ from the proved artifact")
      let _ ← readWeights weightsPath
      IO.println "WGSL_FLOAT_ARTIFACTS_VERIFIED"
  | ["--reference", weightsPath, positionText, t0, t1, t2, t3] =>
      let words ← readWeights weightsPath
      let p := FloatSpec.Correspondence.parameters words
      let position ← readIndex 4 positionText
      let tokens ← #[t0,t1,t2,t3].mapM (readIndex 256)
      let context : FloatSpec.Tokens := fun i => tokens[i.val]!
      let h := FloatSpec.Evaluation.hidden p context position
      let head := FloatSpec.Evaluation.cache (fun j => FloatSpec.headWord p h.get j)
      let output := (List.finRange 256).map fun j => toString (FloatSpec.finish (head.get j) (p.headBias j)).toNat
      IO.println (Lean.Json.mkObj [("specification", Lean.toJson "Project.TinyGpt2.FloatSpec.logits:v1"),
        ("position", Lean.toJson position.val),
        ("hidden",Lean.toJson ((List.finRange 4).map fun i => toString (h.get i).toNat)),
        ("headWords",Lean.toJson ((List.finRange 256).map fun j => toString (head.get j).toNat)),
        ("logits",Lean.toJson output)]).compress
  | _ => throw (IO.userError "expected --check HIDDEN FINISH WEIGHTS or --reference WEIGHTS POSITION T0 T1 T2 T3")
