import Project.Gpt2CachedStep.FrozenLayout
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2CachedStep.Frozen.CachedBlock
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2

def baseCode : Wasm.Program :=
  [.call 2, .localSet 167, .localGet 9, .localSet 170, .call 13, .localSet 171] ++
    CheckedNatMul.program 170 171 ++
    [.localSet 168, .localGet 167, .localGet 168, .addI64, .localTee 169, .localGet 167,
      .ltUI64, .iff 0 1 [.unreachable] [.localGet 169] [] [.i64], .localSet 11]

set_option maxRecDepth 32768 in
theorem emitted_base : func33.take 19 = baseCode := rfl

def baseFrame (frame : Locals) (layer : Nat) : Locals :=
  { frame with
    locals := ((((((frame.locals.set 156 (.i64 (UInt64.ofNat blocksOffset))).set
      159 (.i64 (UInt64.ofNat layer))).set 160 (.i64 (UInt64.ofNat blockWords))).set
      157 (.i64 (UInt64.ofNat (layer * blockWords)))).set
      158 (.i64 (UInt64.ofNat (blocksOffset + layer * blockWords)))).set
      0 (.i64 (UInt64.ofNat (blocksOffset + layer * blockWords))))
    values := [] }

theorem base_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals) (layer : Nat)
    (hParams : frame.params.length = 11) (hLocals : frame.locals.length = 164)
    (hValues : frame.values = []) (hLayerRead : frame.params[9]? = some (.i64 (UInt64.ofNat layer)))
    (hLayer : layer < 12) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q initial (baseFrame frame layer) env) :
    wp «module» (func33.take 19 ++ rest) Q initial frame env := by
  have hMulFit : layer * blockWords < UInt64.size := by
    change layer * 7087872 < 18446744073709551616
    omega
  have hLayer64 : layer < UInt64.size := by change layer < 18446744073709551616; omega
  have hAdd := CheckedNatAdd.guard_of_fits blocksOffset (layer * blockWords)
    (by change 39383808 + layer * 7087872 < 18446744073709551616; omega)
  have hFrame : frame = { frame with values := [] } := Frame.ext _ _ rfl rfl hValues
  rw [emitted_base, hFrame]
  simp only [baseCode, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_call_tw (Layout.blocksOffset_exact env initial) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, hLocals, hLayerRead]
  refine wp_call_tw (Layout.blockWords_exact env _) ?_
  rintro final values ⟨rfl, rfl⟩
  wp_packed_frame [hParams, hLocals]
  apply CheckedNatMul.program_spec 170 171 «module» env final _
    (UInt64.ofNat layer) (UInt64.ofNat blockWords) []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · rw [UInt64.toNat_ofNat_of_lt' hLayer64, UInt64.toNat_ofNat_of_lt' (show blockWords < UInt64.size by decide)]
    exact hMulFit
  wp_packed_frame [hParams, hLocals, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLocals, ← UInt64.ofNat_add]
  exact hNext

#print axioms base_spec

end Project.Gpt2CachedStep.Frozen.CachedBlock
