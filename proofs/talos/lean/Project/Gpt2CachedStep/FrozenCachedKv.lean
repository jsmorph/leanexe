import Project.Gpt2CachedStep.FrozenProgram
import LeanExe.Models.Gpt2.Cached
import Project.ProofKit.PackedWordRead
import Project.ProofKit.PackedFloatFrame
import Project.ProofKit.CheckedNatMulArithmetic
import Project.ProofKit.CheckedNatAddArithmetic

namespace Project.Gpt2CachedStep.Frozen.CachedKv
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2

set_option maxRecDepth 16384 in
theorem cachedKv_exact (env : HostEnv Unit) (initial : Store Unit)
    (cacheOwner qkvOwner cachePtr qkvPtr : UInt64) (cache qkv : ByteArray)
    (layer position source offset : Nat)
    (hCache : ByteArrayAt initial.mem cachePtr.toNat cache)
    (hQkv : ByteArrayAt initial.mem qkvPtr.toNat qkv)
    (hLayer : layer < 12) (hSource : source ≤ position) (hOffset : offset < 1536)
    (hCacheSize : position * 12 * 1536 * 4 ≤ cache.size) (hQkvSize : 2304 * 4 ≤ qkv.size) :
    TerminatesWith env «module» 22 initial
      [.i64 (UInt64.ofNat offset), .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat position),
       .i64 (UInt64.ofNat layer), .i64 (UInt64.ofNat qkv.size), .i64 qkvPtr, .i64 qkvOwner,
       .i64 (UInt64.ofNat cache.size), .i64 cachePtr, .i64 cacheOwner]
      (fun final values => final = initial ∧
        values = [.i64 (cachedKv cache qkv layer position source offset).toUInt64]) := by
  have hPosition64 : position < UInt64.size := by
    have := hCache.1
    change position < 18446744073709551616
    omega
  have hSource64 : source < UInt64.size := hSource.trans_lt hPosition64
  have hCompared : (UInt64.ofNat source < UInt64.ofNat position) ↔ source < position := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt' hSource64,
      UInt64.toNat_ofNat_of_lt' hPosition64]
  refine TerminatesWith.of_wp_entry_for (f := func22Def) rfl ?_
  change wp «module» func22 _ initial
    { params := [.i64 cacheOwner, .i64 cachePtr, .i64 (UInt64.ofNat cache.size),
        .i64 qkvOwner, .i64 qkvPtr, .i64 (UInt64.ofNat qkv.size), .i64 (UInt64.ofNat layer),
        .i64 (UInt64.ofNat position), .i64 (UInt64.ofNat source), .i64 (UInt64.ofNat offset)],
      locals := List.replicate 21 (.i64 0) } env
  simp only [func22]
  wp_packed_frame
  refine wp_iff_cons rfl ?_
  by_cases hEarlier : source < position
  · rw [ite_eq_left (by simp [hCompared, hEarlier])]
    have hMulTwelve := CheckedNatMul.guard_of_nat_fits source 12
      (by have := hCache.1; change source * 12 < 18446744073709551616; omega) (by decide)
    have hAddLayer := CheckedNatAdd.guard_of_fits (source * 12) layer
      (by have := hCache.1; change source * 12 + layer < 18446744073709551616; omega)
    have hMulWidth := CheckedNatMul.guard_of_nat_fits (source * 12 + layer) 1536
      (by have := hCache.1; change (source * 12 + layer) * 1536 < 18446744073709551616; omega) (by decide)
    have hAddOffset := CheckedNatAdd.guard_of_fits ((source * 12 + layer) * 1536) offset
      (by have := hCache.1; change (source * 12 + layer) * 1536 + offset < 18446744073709551616; omega)
    simp only [UInt64.ofNat_add, UInt64.ofNat_mul,
      show UInt64.ofNat 12 = 12 from rfl, show UInt64.ofNat 1536 = 1536 from rfl]
      at hMulTwelve hAddLayer hMulWidth hAddOffset
    have hIndex : (UInt64.ofNat source * 12 + UInt64.ofNat layer) * 1536 + UInt64.ofNat offset =
        UInt64.ofNat ((source * 12 + layer) * 1536 + offset) := by simp
    repeat' first
      | wp_packed_frame
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simp [hMulTwelve, hAddLayer, hMulWidth, hAddOffset])])
    simp only [hIndex]
    refine wp_call_tw (PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
      cacheOwner cachePtr cache ((source * 12 + layer) * 1536 + offset) hCache (by omega)) ?_
    rintro final values ⟨rfl, rfl⟩
    wp_packed_frame
    simp [func22Def, cachedKv, hEarlier, word]
  · rw [ite_eq_right (by simp [hCompared, hEarlier])]
    have hAdd := CheckedNatAdd.guard_of_fits 768 offset
      (by change 768 + offset < 18446744073709551616; omega)
    have hIndex : (768 : UInt64) + UInt64.ofNat offset = UInt64.ofNat (768 + offset) := by simp
    repeat' first
      | wp_packed_frame [hIndex]
      | (refine wp_iff_cons rfl ?_; rw [ite_eq_right (by simpa using hAdd)])
    refine wp_call_tw (PackedWordRead.exact «module» 17 (some 17) rfl rfl env initial
      qkvOwner qkvPtr qkv (768 + offset) hQkv (by omega)) ?_
    rintro final values ⟨rfl, rfl⟩
    wp_packed_frame
    simp [func22Def, cachedKv, hEarlier, word]

#print axioms cachedKv_exact

end Project.Gpt2CachedStep.Frozen.CachedKv
