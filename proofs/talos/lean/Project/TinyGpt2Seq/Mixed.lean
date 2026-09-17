import Project.TinyGpt2Seq.Inference
import Project.TinyGpt2.FloatSpec.Algorithm

/-! The parent sequence hidden function followed by the selected binary32
vocabulary projection and binary64 bias addition. This is the mixed-precision
Lean function; `TinyGpt2Seq.infer` retains its binary64 projection. -/
namespace Project.TinyGpt2Seq.Mixed

def row (x : TinyGpt2.Row) : TinyGpt2.FloatSpec.Vec 4 :=
  TinyGpt2.FloatSpec.vector4 x.x0 x.x1 x.x2 x.x3

def headWord (w : Array UInt64) (x : TinyGpt2.Row) (j : Fin 256) : UInt32 :=
  TinyGpt2.FloatSpec.dot32 (fun i => WGSL.Precision.demote (row x i))
    (fun i => WGSL.Precision.demote w[Layout.head+i.val*256+j.val]!)

def logit (w : Array UInt64) (x : TinyGpt2.Row) (j : Fin 256) : UInt64 :=
  TinyGpt2.FloatSpec.finish (headWord w x j) w[Layout.headBias+j.val]!

def infer (w tokens : Array UInt64) : Array UInt64 :=
  let x := TinyGpt2Seq.hidden w tokens
  Array.ofFn (logit w x)

def inferChecked (w : Array UInt64) (bound : UInt64) (tokens : Array UInt64) : Array UInt64 :=
  if tokensValid tokens then
    let clipped := F64Clip.prepare Layout.size bound w
    if clipped.size == Layout.size then infer clipped tokens else clipped
  else #[]

theorem infer_word (w tokens : Array UInt64) (j : Fin 256) :
    (infer w tokens)[j.val]'(by simp [infer]) = logit w (TinyGpt2Seq.hidden w tokens) j := by
  simp [infer]

theorem checked_word (w tokens : Array UInt64) (bound : UInt64) (j : Fin 256)
    (valid : tokensValid tokens = true)
    (accepted : (F64Clip.prepare Layout.size bound w).size = Layout.size) :
    (inferChecked w bound tokens)[j.val]! =
      logit (F64Clip.prepare Layout.size bound w)
        (TinyGpt2Seq.hidden (F64Clip.prepare Layout.size bound w) tokens) j := by
  simp [inferChecked, valid, accepted, infer]

end Project.TinyGpt2Seq.Mixed
