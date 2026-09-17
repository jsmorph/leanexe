import Project.TinyGpt2.Inference
import Project.F64Clip.Model

namespace Project.TinyGpt2

def inferChecked (w : Array UInt64) (bound t0 t1 t2 t3 : UInt64) : Array UInt64 :=
  if t0 < 256 && t1 < 256 && t2 < 256 && t3 < 256 then
    let clipped := F64Clip.prepare Layout.size bound w
    if clipped.size == Layout.size then infer clipped t0 t1 t2 t3 else clipped
  else #[]

end Project.TinyGpt2
