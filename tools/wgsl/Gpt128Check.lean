import Project.WGSL.GptSequence
import Lean

open Project Project.WGSL

#print axioms GptSequence.finish_interface
#print axioms GptSequence.headWord_eq
#print axioms GptSequence.dispatch_word
#print axioms GptSequence.completes
#print axioms FinishBinary.artifact_exact
#print axioms TinyGpt2Seq.Mixed.infer_word
#print axioms TinyGpt2Seq.Mixed.checked_word

def readWords (path : String) : IO (Array UInt64) := do
  let bytes ← IO.FS.readBinFile path
  unless bytes.size = TinyGpt2Seq.Layout.size*8 do
    throw (IO.userError "expected 2984 binary64 parameter words")
  let mut words := #[]
  for i in [:TinyGpt2Seq.Layout.size] do
    let mut word : UInt64 := 0
    for j in [:8] do word := word ||| (bytes[i*8+j]!.toUInt64 <<< (8*j).toUInt64)
    words := words.push word
  return words

def wordStrings (words : Array UInt64) : Lean.Json := Lean.toJson (words.map fun w => toString w.toNat)
def word32Strings (words : Array UInt32) : Lean.Json := Lean.toJson (words.map fun w => toString w.toNat)

def main (args : List String) : IO Unit := do
  match args with
  | ["--check", finishPath] =>
      unless (← IO.FS.readBinFile finishPath) == FinishBinary.bytes do
        throw (IO.userError "finish Wasm bytes differ from the proved artifact")
      IO.println "WGSL_GPT128_FINISH_VERIFIED"
  | ["--reference", weightsPath, tokensPath, boundText] =>
      let weights ← readWords weightsPath
      let some boundNat := boundText.toNat? | throw (IO.userError "invalid bound word")
      unless boundNat < 2^64 do throw (IO.userError "bound word exceeds 64 bits")
      let bound := UInt64.ofNat boundNat
      let prepared := F64Clip.prepare TinyGpt2Seq.Layout.size bound weights
      unless prepared.size = TinyGpt2Seq.Layout.size do
        throw (IO.userError "parameter preparation rejected weights or bound")
      let tokens ← IO.ofExcept (Lean.fromJson? (← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile tokensPath))) : Except String (Array Nat))
      unless !tokens.isEmpty && tokens.size ≤ 128 && tokens.all (fun t => t < 256) do
        throw (IO.userError "expected 1 to 128 byte tokens")
      let context := tokens.map UInt64.ofNat
      let hidden := TinyGpt2Seq.hidden prepared context
      let h := #[hidden.x0,hidden.x1,hidden.x2,hidden.x3]
      let head : Array UInt32 := Array.ofFn (TinyGpt2Seq.Mixed.headWord prepared hidden)
      let promoted := head.map Precision.promote
      let biases := (Array.finRange 256).map fun j => prepared[TinyGpt2Seq.Layout.headBias+j.val]!
      let logits := (Array.finRange 256).map fun j => Wasm.IEEE64.add promoted[j.val]! biases[j.val]!
      let binary64 := (Array.finRange 256).map fun j => TinyGpt2Seq.logit prepared hidden j.val.toUInt64
      IO.println (Lean.Json.mkObj [
        ("specification",Lean.toJson "Project.TinyGpt2Seq.Mixed.inferChecked:v1"),
        ("hiddenBackend",Lean.toJson "Lean evaluation of Project.TinyGpt2Seq.hidden"),
        ("tokens",Lean.toJson tokens),("boundWord",Lean.toJson (toString bound.toNat)),
        ("preparedWeights",wordStrings prepared),("hidden",wordStrings h),
        ("a",word32Strings (h.map Precision.demote)),
        ("b",word32Strings ((Array.range 1024).map fun i => GptSequence.matrixBuffer prepared i)),
        ("bias",wordStrings biases),("headWords",word32Strings head),
        ("promotedWords",wordStrings promoted),("logits",wordStrings logits),
        ("binary64Logits",wordStrings binary64)]).compress
  | _ => throw (IO.userError "expected --check FINISH or --reference WEIGHTS TOKENS_JSON BOUND_WORD")
