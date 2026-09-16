import Project.ProofKit.FixedFrame
import Interpreter.Wasm.Wp.Call
import CodeLib.Entry

namespace Project.ProofKit.ConstantFunction
open Wasm

def function (value : UInt64) (typeIndex : Option Nat) : Wasm.Function :=
  { locals := [.i64], body := [.constI64 value, .localSet 0, .localGet 0],
    results := [.i64], typeIdx := typeIndex }

theorem exact (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit)
    (index : Nat) (value : UInt64) (typeIndex : Option Nat)
    (hi : module_.imports = [])
    (h : module_.funcs[index]? = some (function value typeIndex)) :
    TerminatesWith env module_ index initial []
      (fun final values => final = initial ∧ values = [.i64 value]) := by
  refine TerminatesWith.of_wp_entry_for (f := function value typeIndex)
    (by simpa [hi] using h) ?_ (by simp [hi])
  change wp module_ [.constI64 value, .localSet 0, .localGet 0] _ initial
    ((function value typeIndex).toLocals []) env
  wp_fixed_frame [function]
  trivial

#print axioms exact
end Project.ProofKit.ConstantFunction
