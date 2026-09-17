import Project.TinyGpt2Checked.Region
import Project.TinyGpt2Infer.Hidden
import Project.TinyGpt2Infer.Logit
import Project.F64Clip.Validation
import Project.F64Clip.Execution

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.TinyGpt2 Project.TinyGpt2Hidden.Spec

theorem hidden_exact (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 position : UInt64)
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256) :
    TerminatesWith env module 80 initial
      [.i64 position, .i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = rowResults (hidden weights t0 t1 t2 t3 position)) :=
  numerical_exact 74 (by decide) (TinyGpt2Infer.Spec.hidden_exact env initial owner pointer weights
    t0 t1 t2 t3 position hWeights hSize ht0 ht1 ht2 ht3)

theorem logit_exact (env : HostEnv Unit) (initial : Store Unit) (owner pointer : UInt64)
    (weights : Array UInt64) (x : Row) (token : UInt64)
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (hToken : token.toNat < 256) :
    TerminatesWith env module 83 initial
      [.i64 token, .i64 x.x3, .i64 x.x2, .i64 x.x1, .i64 x.x0, .i64 pointer, .i64 owner]
      (fun final values => final = initial ∧ values = [.i64 (logit weights x token)]) :=
  numerical_exact 77 (by decide)
    (TinyGpt2Infer.Spec.logit_exact env initial owner pointer weights x token hWeights hSize hToken)

theorem accepted_exact (env : HostEnv Unit) (initial : Store Unit)
    (count bound owner pointer : UInt64) (weights : Array UInt64)
    (hWeights : UInt64Array.At initial pointer weights) :
    TerminatesWith env module 3 initial [.i64 pointer, .i64 owner, .i64 bound, .i64 count]
      (fun final values => final = initial ∧
        values = [.i64 (if F64Clip.accepted count.toNat bound weights then 1 else 0)]) :=
  clipping_exact 3 (by decide)
    (F64Clip.Spec.accepted_exact env initial count bound owner pointer weights hWeights)

theorem clip_exact (env : HostEnv Unit) (initial : Store Unit) (bound x : UInt64) :
    TerminatesWith env module 5 initial [.i64 x, .i64 bound]
      (fun final values => final = initial ∧ values = [.i64 (F64Clip.clip bound x)]) :=
  clipping_exact 5 (by decide) (F64Clip.Spec.clip_exact env initial bound x)

#print axioms hidden_exact
#print axioms logit_exact
#print axioms accepted_exact
end Project.TinyGpt2Checked.Spec
