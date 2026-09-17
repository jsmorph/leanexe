import Project.TinyGpt2Infer.Inference
import Project.TinyGpt2.NumericalLogits

namespace Project.TinyGpt2Infer.Spec
open Wasm CodeLib.IEEE64 Project.TinyGpt2 Project.Runtime Project.ProofKit ArrayPushLayout

theorem infer_real_error (env : HostEnv Unit) (initial : Store Unit)
    (pointer : UInt64) (weights : Array UInt64) (tokens : Real.Tokens)
    (bound lower1 lower2 lowerFinal : ℝ)
    (hb0 : 0 ≤ bound) (hb10 : bound ≤ 10) (hw : WeightsBounded weights bound)
    (hl1 : 0 < lower1) (hl2 : 0 < lower2) (hlFinal : 0 < lowerFinal)
    (hf1 : EmbeddingFloors weights tokens lower1) (hf2 : ResidualFloors weights tokens lower2)
    (hfFinal : FinalFloors weights tokens lowerFinal)
    (start : Nat) (allocations retains releases frees : UInt64)
    (hWeights : UInt64Array.At initial pointer weights) (hSize : 2488 ≤ weights.size)
    (hGlobals : initial.globals.globals =
      [.i64 (UInt64.ofNat start), .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hWeightsBefore : pointer.toNat+8*(weights.size+1) ≤ start)
    (hFit : top start 256 < 4294967296)
    (hMemory : top start 256 ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536) (hCap : initial.mem.pages ≤ initial.memoryCap module 0) :
    let output := infer weights (tokenWords tokens 0) (tokenWords tokens 1) (tokenWords tokens 2) (tokenWords tokens 3)
    TerminatesWith env module 78 initial
      [.i64 (tokenWords tokens 3), .i64 (tokenWords tokens 2), .i64 (tokenWords tokens 1),
        .i64 (tokenWords tokens 0), .i64 pointer]
      (fun final values => values = [.i64 (node start 256).root] ∧
        UInt64Array.At final (node start 256).root output ∧
        UInt64Array.At final pointer weights ∧ final.mem.pages = initial.mem.pages ∧
        (∀ address : Nat, address < start → final.mem.bytes address = initial.mem.bytes address) ∧
        final = { initial with mem := final.mem, globals := final.globals } ∧
        ∀ j : Fin 256, Affine.Bounded output[j.val]! 1260 ∧
          |value output[j.val]!-Real.logits (parameters weights) tokens 3 j| ≤
            ErrorBudget.logits bound lower1 lower2 lowerFinal) := by
  have h := infer_exact env initial pointer weights (tokenWords tokens 0) (tokenWords tokens 1)
    (tokenWords tokens 2) (tokenWords tokens 3) start allocations retains releases frees hWeights hSize
    (tokenWords_valid tokens 0) (tokenWords_valid tokens 1) (tokenWords_valid tokens 2) (tokenWords_valid tokens 3)
    hGlobals hWeightsBefore hFit hMemory hPages hCap
  refine TerminatesWith.mono h ?_
  rintro final values ⟨hv, ho, hw', hp, hbytes, hstore⟩
  refine ⟨hv, ho, hw', hp, hbytes, hstore, ?_⟩
  intro j
  exact ⟨runtime_infer_bounded weights bound hb0 hb10 hw (tokenWords tokens) (tokenWords_valid tokens) j,
    infer_accuracy weights bound lower1 lower2 lowerFinal hb0 hb10 hw tokens
      hl1 hl2 hlFinal hf1 hf2 hfFinal j⟩

#print axioms infer_real_error
end Project.TinyGpt2Infer.Spec
