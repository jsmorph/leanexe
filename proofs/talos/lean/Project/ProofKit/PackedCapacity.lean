import Project.ProofKit.FixedArrayCapacity

namespace Project.ProofKit.PackedCapacity
open Wasm FixedArrayCapacity

def rounded (bytes : UInt64) : UInt64 := ((bytes + 7) / 8) * 8

def capacity (bytes : UInt64) : UInt64 :=
  if rounded bytes < 8 then 8 else rounded bytes

def capacityNat (bytes : Nat) : Nat := max 8 (((bytes + 7) / 8) * 8)

theorem capacity_toNat (bytes : Nat) (hbytes : bytes ≤ 2^32) :
    (capacity (UInt64.ofNat bytes)).toNat = capacityNat bytes := by
  have hround : (rounded (UInt64.ofNat bytes)).toNat = (bytes + 7) / 8 * 8 := by
    simp only [rounded, UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add,
      UInt64.toNat_ofNat', UInt64.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
    omega
  unfold capacity capacityNat
  split <;> rename_i h
  · rw [UInt64.lt_iff_toNat_lt, hround] at h
    change (bytes + 7) / 8 * 8 < 8 at h
    change 8 = max 8 _
    omega
  · rw [UInt64.lt_iff_toNat_lt, hround] at h
    change ¬(bytes + 7) / 8 * 8 < 8 at h
    rw [hround]
    omega

theorem capacityNat_ge (bytes : Nat) : bytes ≤ capacityNat bytes := by
  unfold capacityNat
  omega

theorem capacityNat_le (bytes : Nat) : capacityNat bytes ≤ bytes + 8 := by
  unfold capacityNat
  omega

def program (bytesLocal capacityLocal : Nat) : Wasm.Program :=
  [.localGet bytesLocal, .constI64 7, .addI64, .constI64 8, .divUI64,
    .constI64 8, .mulI64, .localSet capacityLocal,
    .localGet capacityLocal, .constI64 8, .ltUI64,
    .iff 0 0 [.constI64 8, .localSet capacityLocal] []]

theorem program_spec (bytesLocal capacityLocal : Nat) (bytes : UInt64)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (hBytes : frame.get bytesLocal = some (.i64 bytes)) (hValues : frame.values = [])
    (hLower : frame.params.length ≤ capacityLocal) (hValid : frame.validIndex capacityLocal)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q store (capacityFrame frame capacityLocal (capacity bytes)) env) :
    wp module_ (program bytesLocal capacityLocal ++ rest) Q store frame env := by
  have hBound : capacityLocal < frame.params.length + frame.locals.length := hValid
  have hNotParam : ¬capacityLocal < frame.params.length := by omega
  have hIndex : capacityLocal - frame.params.length < frame.locals.length := by omega
  simp only [program, List.cons_append, List.nil_append, wp_localGet_cons, hBytes, hValues,
    wp_constI64_cons, wp_addI64_cons, wp_divUI64_cons, wp_mulI64_cons, wp_localSet_cons,
    Locals.set?, hNotParam, hBound, ite_false, ite_true]
  simp [wp_simp, hNotParam, hBound, hIndex]
  refine wp_iff_cons rfl ?_
  by_cases hSmall : rounded bytes < 8
  · have hSmall' := hSmall
    unfold rounded at hSmall'
    simpa [wp_simp, rounded, capacity, capacityFrame, hSmall, hSmall', hValues,
      hNotParam, hBound, hIndex] using hNext
  · have hSmall' := hSmall
    unfold rounded at hSmall'
    simpa [wp_simp, rounded, capacity, capacityFrame, hSmall, hSmall', hValues,
      hNotParam, hBound, hIndex] using hNext

#print axioms capacity_toNat
#print axioms program_spec

end Project.ProofKit.PackedCapacity
