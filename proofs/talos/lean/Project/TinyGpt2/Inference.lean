import Project.TinyGpt2.Model

namespace Project.TinyGpt2

def infer (w : Array UInt64) (t0 t1 t2 t3 : UInt64) : Array UInt64 := Id.run do
  let x := hidden w t0 t1 t2 t3 3
  let mut output := #[]
  for token in [:256] do
    output := output.push (logit w x token.toUInt64)
  return output

end Project.TinyGpt2
