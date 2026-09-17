import Project.TinyGpt2Seq.Model
import Project.F64Clip.Model

namespace Project.TinyGpt2Seq

def infer (w tokens : Array UInt64) : Array UInt64 := Id.run do
  let x := hidden w tokens
  let mut output := #[]
  for token in [:256] do
    output := output.push (logit w x token.toUInt64)
  return output

def tokensValid (tokens : Array UInt64) : Bool :=
  !tokens.isEmpty && decide (tokens.size ≤ Layout.context) && tokens.all (fun t => t < 256)

def inferChecked (w : Array UInt64) (bound : UInt64) (tokens : Array UInt64) : Array UInt64 :=
  if tokensValid tokens then
    let clipped := F64Clip.prepare Layout.size bound w
    if clipped.size == Layout.size then infer clipped tokens else clipped
  else #[]

end Project.TinyGpt2Seq
