import Project.TinyGpt2Hidden.Normalization
import Project.TinyGpt2Hidden.Attention
import Project.TinyGpt2Hidden.Projection
import Project.TinyGpt2Hidden.Contract
import Project.TinyGpt2Hidden.Embedding
import Project.TinyGpt2Hidden.HiddenModel
import Project.TinyGpt2Hidden.HiddenCode
import Project.ProofKit.ProofStep
import Project.ProofKit.ExactCall
import Project.TinyGpt2Hidden.Composition

namespace Project.TinyGpt2Hidden.Spec
open Wasm Project.TinyGpt2 Project.ProofKit HiddenCode

set_option Elab.async false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192

theorem hidden_exact_for (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 position : UInt64)
    (expected : Row) (hexpected : hidden weights t0 t1 t2 t3 position = expected)
    (ha : UInt64Array.At initial pointer weights) (hb : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256) :
    TerminatesWith env Project.TinyGpt2Hidden.module 74 initial
      [.i64 position, .i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 pointer]
      (fun final values => final = initial ∧
        values = rowResults expected) := by
  proof_step =>
    refine TerminatesWith.of_wp_entry_for (f := func74Def) rfl ?_ (by decide)
    change wp Project.TinyGpt2Hidden.module func74 _ initial
      (func74Def.toLocals [.i64 pointer, .i64 t0, .i64 t1, .i64 t2, .i64 t3, .i64 position]) env
    rw [program_eq]
    unfold tail0
  tiny_hidden_steps Project.TinyGpt2Hidden Project.TinyGpt2Hidden.HiddenCode
    (fun (i : Nat) (_ : i < 74) => id) (0)
    [env, initial, pointer, weights, t0, t1, t2, t3, position, expected, hexpected]
    [ha, hb, ht0, ht1, ht2, ht3]

theorem hidden_exact (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (weights : Array UInt64) (t0 t1 t2 t3 position : UInt64)
    (ha : UInt64Array.At initial pointer weights) (hb : 2488 ≤ weights.size)
    (ht0 : t0.toNat < 256) (ht1 : t1.toNat < 256)
    (ht2 : t2.toNat < 256) (ht3 : t3.toNat < 256) :
    TerminatesWith env Project.TinyGpt2Hidden.module 74 initial
      [.i64 position, .i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 pointer]
      (fun final values => final = initial ∧
        values = rowResults (hidden weights t0 t1 t2 t3 position)) :=
  hidden_exact_for env initial pointer weights t0 t1 t2 t3 position _ rfl ha hb ht0 ht1 ht2 ht3

#print axioms hidden_exact
end Project.TinyGpt2Hidden.Spec
