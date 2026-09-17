import Project.TinyGpt2Checked.Entry
import Project.TinyGpt2.CheckedBounds

namespace Project.TinyGpt2Checked.Spec
open Wasm CodeLib.IEEE64 Project.ProofKit Project.TinyGpt2

theorem inferChecked_real_error (env : HostEnv Unit) (initial : Store Unit)
    (pointer bound base : UInt64) (weights : Array UInt64) (tokens : Real.Tokens)
    (ha : F64Clip.accepted Layout.size bound weights = true)
    (lower1 lower2 lowerFinal : ℝ)
    (hl1 : 0 < lower1) (hl2 : 0 < lower2) (hlFinal : 0 < lowerFinal)
    (hf1 : EmbeddingFloors (F64Clip.prepare Layout.size bound weights) tokens lower1)
    (hf2 : ResidualFloors (F64Clip.prepare Layout.size bound weights) tokens lower2)
    (hfFinal : FinalFloors (F64Clip.prepare Layout.size bound weights) tokens lowerFinal)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : UInt64Array.At initial pointer weights)
    (hBefore : pointer.toNat+8*(weights.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(weights.size+1)+277560 < 4294967296)
    (hMemory : base.toNat+48+8*(weights.size+1)+277560 ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0) :
    let output := inferChecked weights bound (tokenWords tokens 0) (tokenWords tokens 1)
      (tokenWords tokens 2) (tokenWords tokens 3)
    TerminatesWith env module 85 initial
      [.i64 (tokenWords tokens 3), .i64 (tokenWords tokens 2), .i64 (tokenWords tokens 1),
        .i64 (tokenWords tokens 0), .i64 bound, .i64 pointer]
      (fun final values => ∃ root : UInt64, values = [.i64 root] ∧
        UInt64Array.At final root output ∧ UInt64Array.At final pointer weights ∧
        final.mem.pages = initial.mem.pages ∧
        (∀ address : Nat, address < base.toNat → final.mem.bytes address = initial.mem.bytes address) ∧
        final = { initial with mem := final.mem, globals := final.globals } ∧
        ∀ j : Fin 256, Affine.Bounded output[j.val]! 1260 ∧
          |value output[j.val]!-Real.logits (parameters (F64Clip.prepare Layout.size bound weights)) tokens 3 j| ≤
            ErrorBudget.logits (value bound) lower1 lower2 lowerFinal) := by
  refine TerminatesWith.mono (inferChecked_exact env initial pointer bound
    (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3)
    base weights allocations retains releases frees hGlobals hInput hBefore hFit hMemory hPages hCap) ?_
  rintro final values ⟨root, hv, ho, hw, hp, hbytes, hstore⟩
  refine ⟨root, hv, ho, hw, hp, hbytes, hstore, ?_⟩
  intro j
  refine ⟨inferChecked_bounded weights bound tokens ha j, ?_⟩
  rw [inferChecked_accept weights bound tokens ha]
  have hb := ((F64Clip.accepted_iff Layout.size bound weights).mp ha).2.1
  exact infer_accuracy _ (value bound) lower1 lower2 lowerFinal hb.2.1 hb.2.2
    (prepared_weights_bounded bound weights ha) tokens hl1 hl2 hlFinal hf1 hf2 hfFinal j

#print axioms inferChecked_real_error
end Project.TinyGpt2Checked.Spec
