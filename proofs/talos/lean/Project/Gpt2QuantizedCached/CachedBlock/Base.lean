import Project.Gpt2QuantizedCached.Layout
import Project.ProofKit.CheckedNatMul
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def baseCode : Wasm.Program :=
  [.call 4, .localSet 196, .localGet 9, .localSet 199, .call 19, .localSet 200] ++
    CheckedNatMul.program 199 200 ++
    [.localSet 197, .localGet 196, .localGet 197, .addI64, .localTee 198, .localGet 196,
      .ltUI64, .iff 0 1 [.unreachable] [.localGet 198] [] [.i64], .localSet 11]

set_option maxRecDepth 32768 in
theorem emitted_base : func54.take 19 = baseCode := rfl

def baseFrame (frame : Locals) (layer : Nat) : Locals :=
  { frame with
    locals := ((((((frame.locals.set 185 (.i64 (UInt64.ofNat blocksOffset))).set
      188 (.i64 (UInt64.ofNat layer))).set 189 (.i64 (UInt64.ofNat blockBytes))).set
      186 (.i64 (UInt64.ofNat (layer * blockBytes)))).set
      187 (.i64 (UInt64.ofNat (blocksOffset + layer * blockBytes)))).set
      0 (.i64 (UInt64.ofNat (blocksOffset + layer * blockBytes))))
    values := [] }

theorem base_spec (env : HostEnv Unit) (initial : Store Unit) (frame : Locals) (layer : Nat)
    (hParams : frame.params.length = 11) (hLocals : frame.locals.length = 193)
    (hValues : frame.values = []) (hLayerRead : frame.params[9]? = some (.i64 (UInt64.ofNat layer)))
    (hLayer : layer < 12) (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q initial (baseFrame frame layer) env) :
    wp «module» (func54.take 19 ++ rest) Q initial frame env := by
  have hMulFit : layer * blockBytes < UInt64.size := by
    change layer * 7145472 < 18446744073709551616
    omega
  have hLayer64 : layer < UInt64.size := by change layer < 18446744073709551616; omega
  have hAdd := CheckedNatAdd.guard_of_fits blocksOffset (layer * blockBytes)
    (by change 41944164 + layer * 7145472 < 18446744073709551616; omega)
  have hFrame : frame = { frame with values := [] } := Frame.ext _ _ rfl rfl hValues
  rw [emitted_base, hFrame]
  simp only [baseCode, List.append_assoc, List.cons_append, List.nil_append]
  refine wp_call_tw (Layout.blocksOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLocals, hLayerRead]
  refine wp_call_tw (Layout.blockBytes_exact env _) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLocals]
  apply CheckedNatMul.program_spec 199 200 «module» env initial _
    (UInt64.ofNat layer) (UInt64.ofNat blockBytes) []
  · rfl
  · simp [Locals.get, hParams, hLocals]
  · simp [Locals.get, hParams, hLocals]
  · rw [UInt64.toNat_ofNat_of_lt' hLayer64, UInt64.toNat_ofNat_of_lt' (show blockBytes < UInt64.size by decide)]
    exact hMulFit
  wp_packed_frame [hParams, hLocals, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLocals, ← UInt64.ofNat_add]
  exact hNext

#print axioms base_spec

end Project.Gpt2QuantizedCached.CachedBlock
