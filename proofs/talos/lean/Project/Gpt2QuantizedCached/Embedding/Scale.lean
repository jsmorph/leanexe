import Project.Gpt2QuantizedCached.Embedding.Word

set_option maxRecDepth 32768

namespace Project.Gpt2QuantizedCached.Embedding
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def scaleFrame (frame : Locals) (ptr : UInt64) (weights : ByteArray) (token : UInt32) : Locals :=
  { frame with
    locals := (((((((((frame.locals.set 7 (.i64 ptr)).set 8 (.i64 (UInt64.ofNat weights.size))).set
      10 (.i64 (UInt64.ofNat tokenScaleOffset))).set 13 (.i64 token.toUInt64)).set
      14 (.i64 4)).set 11 (.i64 (token.toUInt64 * 4))).set
      12 (.i64 (UInt64.ofNat tokenScaleOffset + token.toUInt64 * 4))).set
      9 (.i64 (UInt64.ofNat tokenScaleOffset + token.toUInt64 * 4))).set
      0 (.i64 (scale weights token).toUInt64))
    values := [] }

theorem scale_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (weights : ByteArray) (token : UInt32) (position : Nat) (frame : Locals)
    (hWeights : ByteArrayAt initial.mem ptr.toNat weights)
    (hScaleSize : tokenScaleOffset + token.toNat * 4 + 4 ≤ weights.size)
    (hToken : token.toNat < 50257)
    (hParams : frame.params = parameters owner ptr weights token position)
    (hLength : frame.locals.length = 22) (hValues : frame.values = [])
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q initial (scaleFrame frame ptr weights token) env) :
    wp «module» (func30.take 28 ++ rest) Q initial frame env := by
  simp only [parameters] at hParams
  have hMul : ¬ (-1 : UInt64) / 4 < UInt64.ofNat token.toNat := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' (by
      change token.toNat < 18446744073709551616; omega)]
    change ¬ 4611686018427387903 < token.toNat
    omega
  have hAdd := CheckedNatAdd.guard_of_fits tokenScaleOffset (token.toNat * 4)
    (by change 38597408 + token.toNat * 4 < 18446744073709551616; omega)
  simp only [func30, List.take, List.cons_append, List.nil_append]
  wp_packed_frame [hParams, hLength, hValues]
  refine wp_call_tw (Layout.tokenScaleOffset_exact env initial) ?_
  rintro final values ⟨hFinal, rfl⟩
  subst final
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by decide)]
  wp_packed_frame [hParams, hLength]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hMul)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_mul]
  refine wp_iff_cons rfl ?_
  rw [ite_eq_right (by simpa using hAdd)]
  wp_packed_frame [hParams, hLength, ← UInt64.ofNat_add]
  apply PackedWordAccess.guard_spec «module» env initial _ ptr weights
    (tokenScaleOffset + token.toNat * 4) 12 13 14 [] hWeights hScaleSize
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength]
  · simp [Locals.get, hLength, UInt64.ofNat_add, UInt64.ofNat_mul]
  · simp [UInt64.ofNat_add, UInt64.ofNat_mul]
  wp_packed_frame [hParams, hLength]
  simpa only [scaleFrame, scale, hParams, parameters, UInt64.ofNat_uInt32ToNat] using hNext

#print axioms scale_spec

end Project.Gpt2QuantizedCached.Embedding
