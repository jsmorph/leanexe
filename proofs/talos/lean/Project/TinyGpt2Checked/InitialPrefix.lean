import Project.TinyGpt2Checked.Components
import Project.TinyGpt2Checked.OutputCode
import Project.ProofKit.FixedArrayCapacity
import Project.ProofKit.FixedFrame

namespace Project.TinyGpt2Checked.Spec
open Project.TinyGpt2Infer
open Wasm Project.TinyGpt2 Project.ProofKit Project.TinyGpt2Hidden.Spec

def inferenceParams (owner pointer t0 t1 t2 t3 : UInt64) : List Wasm.Value :=
  [.i64 owner, .i64 pointer, .i64 t0, .i64 t1, .i64 t2, .i64 t3]

def inferenceSaved (owner pointer t0 t1 t2 t3 : UInt64) (x : Row) : List Wasm.Value :=
  [.i64 owner, .i64 pointer, .i64 t0, .i64 t1, .i64 t2, .i64 t3, .i64 3,
    .i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3,
    .i64 x.x0, .i64 x.x1, .i64 x.x2, .i64 x.x3] ++ List.replicate 30 (.i64 0)

def initialAllocationFrame (owner pointer t0 t1 t2 t3 : UInt64) (x : Row)
    (need previous current capacity next result : UInt64) : Locals :=
  FixedArraySearch.frame (inferenceParams owner pointer t0 t1 t2 t3)
    (inferenceSaved owner pointer t0 t1 t2 t3 x) (List.replicate 12 (.i64 0))
    need previous current capacity next result

def inferenceHiddenPrefix : Wasm.Program :=
  [.localGet 0, .localSet 6, .localGet 1, .localSet 7,
   .localGet 2, .localSet 8, .localGet 3, .localSet 9,
   .localGet 4, .localSet 10, .localGet 5, .localSet 11,
   .constI64 3, .localSet 12,
   .localGet 6, .localGet 7, .localGet 8, .localGet 9,
   .localGet 10, .localGet 11, .localGet 12, .call 80,
   .localSet 16, .localSet 15, .localSet 14, .localSet 13,
   .localGet 13, .localSet 17, .localGet 14, .localSet 18,
   .localGet 15, .localSet 19, .localGet 16, .localSet 20]

theorem inference_prefix_shape : func84.take 52 =
    inferenceHiddenPrefix ++ FixedArrayCapacity.constantProgram 0 1 51 := rfl

theorem inference_prefix_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 : UInt64)
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module rest Q initial
      (initialAllocationFrame owner pointer t0 t1 t2 t3 (hidden weights t0 t1 t2 t3 3) 8 0 0 0 0 0) env) :
    wp module (func84.take 52 ++ rest) Q initial
      (func84Def.toLocals (inferenceParams owner pointer t0 t1 t2 t3)) env := by
  rw [inference_prefix_shape]
  simp only [inferenceHiddenPrefix, List.cons_append, List.nil_append]
  wp_fixed_frame [func84Def, inferenceParams, List.map, ValueType.zero, List.replicate]
  refine wp_call_exact_append (hidden_exact env initial owner pointer weights t0 t1 t2 t3 3
    hWeights hSize ht0 ht1 ht2 ht3) rfl rfl rfl [] ?_ ?_
  · rfl
  wp_fixed_frame [rowResults, List.append_nil]
  apply FixedArrayCapacity.constantProgram_spec 0 1 51 module env initial _ rfl
    (by change 6 ≤ 51; decide) (by change 51 < 6 + 63; decide)
  have hCapacity : FixedArrayCapacity.normalizedCapacity 0 1 = 8 := by decide
  simpa only [initialAllocationFrame, inferenceParams, inferenceSaved, FixedArraySearch.frame,
    FixedArrayCapacity.capacityFrame, hCapacity, List.length_cons, List.length_nil,
    Nat.reduceSub, List.set, List.replicate, List.cons_append, List.nil_append] using hNext

#print axioms inference_prefix_spec
end Project.TinyGpt2Checked.Spec
