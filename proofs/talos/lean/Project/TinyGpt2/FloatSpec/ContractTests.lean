import Project.TinyGpt2.FloatSpec.Algorithm

namespace Project.TinyGpt2.FloatSpec.ContractTests

/-- Four negative zeros stay negative under the balanced binary64 sum. -/
theorem negative_zero : sum4 (fun _ => 0x8000000000000000) = 0x8000000000000000 := by decide +kernel

/-- The head's initial positive-zero add is observable. -/
theorem head_zero_sign : dot32 (fun _ => 0x80000000) (fun _ => 0x3F800000) = 0 := by decide +kernel

theorem head_subnormals : dot32 (fun _ => 1) (fun _ => 0x3F800000) = 4 := by decide +kernel

def cancellation : Vec 4 := vector4 0x4340000000000000 0x3FF0000000000000
  0x3FF0000000000000 0xC340000000000000

theorem balanced_order : sum4 cancellation = 0x3FF0000000000000 := by decide +kernel

theorem sequential_differs :
    (List.finRange 4).foldl (fun a i => Wasm.IEEE64.add a (cancellation i)) 0 = 0 := by decide +kernel

theorem exponential_cutoff : expNegative 0xC050000000000001 = 0 := by decide +kernel

theorem canonical_nan : Wasm.IEEE64.add 0x7FF0000000000000 0xFFF0000000000000 =
    Wasm.IEEE64.canonicalNaN := by decide +kernel

#print axioms negative_zero
#print axioms head_zero_sign
#print axioms head_subnormals
#print axioms balanced_order
#print axioms sequential_differs
#print axioms exponential_cutoff
#print axioms canonical_nan
end Project.TinyGpt2.FloatSpec.ContractTests
