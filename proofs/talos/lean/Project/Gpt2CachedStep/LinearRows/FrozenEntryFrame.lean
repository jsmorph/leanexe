import Project.Gpt2CachedStep.LinearRows.FrozenLoop
import Project.ProofKit.PackedAllocation
import Project.ProofKit.PackedCapacity
import Project.ProofKit.CheckedNatMul

namespace Project.Gpt2CachedStep.Frozen.LinearRows

open Wasm Project.Common Project.ProofKit PackedFloatFrame

def entryFrame (params : List Value) : Locals :=
  { params := params, locals := List.replicate 48 (.i64 0) }

def saved (count : Nat) : List Value :=
  [.i64 (UInt64.ofNat (4 * count))] ++ List.replicate 31 (.i64 0) ++
    [.i64 (UInt64.ofNat (4 * count)), .i64 4]

def sizeFrame (params : List Value) (rows outputWidth : Nat) : Locals :=
  FixedArraySearch.frame params (saved (rows * outputWidth)) (List.replicate 8 (.i64 0))
    (UInt64.ofNat rows) (UInt64.ofNat outputWidth) 0 0 0 0

set_option maxRecDepth 32768 in
theorem size_prefix (env : HostEnv Unit) (store : Store Unit)
    (params : List Value) (rows outputWidth : Nat)
    (hparams : params.length = 11)
    (hrows : params[10]? = some (.i64 (UInt64.ofNat rows)))
    (hwidth : params[9]? = some (.i64 (UInt64.ofNat outputWidth)))
    (hcount : 4 * (rows * outputWidth) ≤ 2^32)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : wp «module» rest Q store (sizeFrame params rows outputWidth) env) :
    wp «module» (func21.take 18 ++ rest) Q store (entryFrame params) env := by
  have hsplit : func21.take 18 =
      [.localGet 10, .localSet 45, .localGet 9, .localSet 46] ++
      CheckedNatMul.program 45 46 ++ [.localSet 43, .constI64 4, .localSet 44] ++
      CheckedNatMul.program 43 44 ++ [.localSet 11, .localGet 11, .localSet 43] := rfl
  have hproduct : UInt64.ofNat rows * UInt64.ofNat outputWidth = UInt64.ofNat (rows * outputWidth) := by simp
  have hbytes : UInt64.ofNat (rows * outputWidth) * 4 = UInt64.ofNat (4 * (rows * outputWidth)) := by
    simp [Nat.mul_comm]
  rw [hsplit]
  simp only [List.append_assoc, entryFrame, List.cons_append, List.nil_append]
  wp_packed_frame [hparams, hrows, hwidth]
  apply CheckedNatMul.program_spec 45 46 «module» env store _
    (UInt64.ofNat rows) (UInt64.ofNat outputWidth) []
  · rfl
  · simp [Locals.get, hparams]
  · simp [Locals.get, hparams]
  · apply lt_of_le_of_lt (Nat.mul_le_mul (Nat.mod_le ..) (Nat.mod_le ..))
    change rows * outputWidth < 18446744073709551616
    omega
  wp_packed_frame [hparams, hproduct]
  apply CheckedNatMul.program_spec 43 44 «module» env store _
    (UInt64.ofNat (rows * outputWidth)) 4 []
  · rfl
  · simp [Locals.get, hparams]
  · simp [Locals.get, hparams]
  · simp only [UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    change _ < 18446744073709551616
    omega
  wp_packed_frame [hparams, hbytes]
  simpa [sizeFrame, FixedArraySearch.frame, saved] using hnext

theorem capacity_prefix (env : HostEnv Unit) (store : Store Unit)
    (params : List Value) (rows outputWidth : Nat) (hparams : params.length = 11)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hnext : wp «module» rest Q store
      (FixedArraySearch.frame params (saved (rows * outputWidth)) (List.replicate 8 (.i64 0))
        (PackedCapacity.capacity (UInt64.ofNat (4 * (rows * outputWidth))))
        (UInt64.ofNat outputWidth) 0 0 0 0) env) :
    wp «module» ((func21.drop 18).take 12 ++ rest) Q store (sizeFrame params rows outputWidth) env := by
  have hregion : (func21.drop 18).take 12 = PackedCapacity.program 43 45 := rfl
  rw [hregion]
  apply PackedCapacity.program_spec 43 45 (UInt64.ofNat (4 * (rows * outputWidth)))
    «module» env store (sizeFrame params rows outputWidth)
  · simp [sizeFrame, FixedArraySearch.frame, saved, Locals.get, hparams]
  · rfl
  · simp [sizeFrame, FixedArraySearch.frame, hparams]
  · simp [Locals.validIndex, sizeFrame, FixedArraySearch.frame, saved, hparams]
  simpa [FixedArrayCapacity.capacityFrame, sizeFrame, FixedArraySearch.frame, saved, Locals.set,
    hparams] using hnext

set_option maxRecDepth 32768 in
theorem emitted_allocation : (func21.drop 30).take 15 = PackedAllocation.program 45 := rfl

theorem return_suffix (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (pointer length : UInt64) (hparams : frame.params.length = 11)
    (hlocals : frame.locals.length = 48) (hvalues : frame.values = [])
    (hpointer : frame.get 44 = some (.i64 pointer))
    (hlength : frame.locals[0]? = some (.i64 length))
    (Q : Assertion Unit)
    (hnext : ∀ result, result.values = [.i64 length, .i64 pointer, .i64 pointer] → Q (.Fallthrough store result)) :
    wp «module» (func21.drop 50) Q store frame env := by
  have hreturn : func21.drop 50 =
      [.localGet 44, .localSet 39, .localGet 39, .localSet 40, .localGet 39, .localSet 41,
        .localGet 11, .localSet 42, .localGet 40, .localGet 41, .localGet 42] := rfl
  have hp := Frame.internal_getElem?_of_get frame 11 33 (.i64 pointer)
    hparams (by omega) hpointer
  rw [hreturn]
  wp_packed_frame [hparams, hlocals, hvalues, hp, hlength]
  exact hnext _ rfl

#print axioms size_prefix
#print axioms capacity_prefix
#print axioms return_suffix

end Project.Gpt2CachedStep.Frozen.LinearRows
