import Project.EulerRiemann.Program
import Project.EulerRiemann.Traversal
import Project.EulerRiemann.Geometry
import Project.ProofKit.Control

namespace Project.EulerRiemann.Execution
open Wasm

set_option maxHeartbeats 1000000

def boolWord (value : Bool) : UInt64 := if value then 1 else 0

macro "neighbor_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func30Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem neighborIndex_exact (env : HostEnv Unit) (initial : Store Unit)
    (n index : Nat) (axis forward : Bool)
    (hn : 2 ≤ n ∧ n ≤ 800) (hi : index < n * n) :
    TerminatesWith env Project.EulerRiemann.«module» 30 initial
      [.i64 (boolWord forward), .i64 (boolWord axis),
        .i64 (UInt64.ofNat index), .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = [.i64 (UInt64.ofNat (Traversal.neighborIndex n index axis forward))]) := by
  have hnSquare : n * n ≤ 640000 := by nlinarith [hn.2]
  have hn64 : n < UInt64.size := by change n < 18446744073709551616; omega
  have hi64 : index < UInt64.size := by change index < 18446744073709551616; omega
  have hnNat := UInt64.toNat_ofNat_of_lt' hn64
  have hiNat := UInt64.toNat_ofNat_of_lt' hi64
  have hnWord : UInt64.ofNat n ≠ 0 := by
    intro heq
    have := congrArg UInt64.toNat heq
    simp only [hnNat, UInt64.toNat_zero] at this
    omega
  have hDivBound : index / n < n := (Nat.div_lt_iff_lt_mul (by omega)).mpr hi
  have hModBound : index % n < n := Nat.mod_lt index (by omega)
  have hDiv : UInt64.ofNat index / UInt64.ofNat n = UInt64.ofNat (index / n) := by
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_div, hnNat, hiNat,
      UInt64.toNat_ofNat_of_lt' (show index / n < UInt64.size by omega)]
  have hMod : UInt64.ofNat index % UInt64.ofNat n = UInt64.ofNat (index % n) := by
    apply UInt64.toNat.inj
    simp only [UInt64.toNat_mod, hnNat, hiNat,
      UInt64.toNat_ofNat_of_lt' (show index % n < UInt64.size by omega)]
  let coordinate := if axis then index / n else index % n
  let stride := if axis then n else 1
  have hc : coordinate < n := by cases axis <;> simp_all [coordinate]
  have hs : 0 < stride ∧ stride ≤ n := by
    cases axis <;> simp only [stride, Bool.false_eq_true, reduceIte] <;> omega
  have hcNat := UInt64.toNat_ofNat_of_lt' (show coordinate < UInt64.size by omega)
  have hsNat := UInt64.toNat_ofNat_of_lt' (show stride < UInt64.size by omega)
  have hcNextNat := UInt64.toNat_ofNat_of_lt'
    (show coordinate + 1 < UInt64.size by change coordinate + 1 < 18446744073709551616; omega)
  have hiNextNat := UInt64.toNat_ofNat_of_lt'
    (show index + stride < UInt64.size by change index + stride < 18446744073709551616; omega)
  have hcAdd : UInt64.ofNat coordinate + 1 = UInt64.ofNat (coordinate + 1) :=
    (UInt64.ofNat_add coordinate 1).symm
  have hiAdd : UInt64.ofNat index + UInt64.ofNat stride = UInt64.ofNat (index + stride) :=
    (UInt64.ofNat_add index stride).symm
  have hcNoOverflow : ¬ UInt64.ofNat (coordinate + 1) < UInt64.ofNat coordinate := by
    simp only [UInt64.lt_iff_toNat_lt, hcNextNat, hcNat]
    omega
  have hiNoOverflow : ¬ UInt64.ofNat (index + stride) < UInt64.ofNat index := by
    simp only [UInt64.lt_iff_toNat_lt, hiNextNat, hiNat]
    omega
  have hForward : (UInt64.ofNat (coordinate + 1) < UInt64.ofNat n) ↔ coordinate + 1 < n := by
    simp only [UInt64.lt_iff_toNat_lt, hcNextNat, hnNat]
  have hZero : (UInt64.ofNat coordinate = 0) ↔ coordinate = 0 := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      simpa only [hcNat, UInt64.toNat_zero] using this
    · intro h
      rw [h]
      rfl
  have hLower : (UInt64.ofNat index < UInt64.ofNat stride) ↔ index < stride := by
    simp only [UInt64.lt_iff_toNat_lt, hiNat, hsNat]
  have hSub (h : stride ≤ index) :
      UInt64.ofNat index - UInt64.ofNat stride = UInt64.ofNat (index - stride) := by
    apply UInt64.toNat.inj
    rw [UInt64.toNat_sub_of_le _ _ (by simpa only [UInt64.le_iff_toNat_le, hiNat, hsNat] using h),
      hiNat, hsNat, UInt64.toNat_ofNat_of_lt' (show index - stride < UInt64.size by omega)]
  have hBack (h : coordinate ≠ 0) : stride ≤ index := by
    cases axis
    · simp only [coordinate, stride, Bool.false_eq_true, reduceIte] at *
      have : 0 < index := by
        by_contra hpos
        have hz : index = 0 := by omega
        simp [hz] at h
      omega
    · simp only [coordinate, stride, reduceIte] at *
      have hmul := Nat.mul_le_mul_left n (show 1 ≤ index / n by omega)
      have hdiv := Nat.mul_div_le index n
      simpa only [Nat.mul_one] using le_trans hmul hdiv
  refine TerminatesWith.of_wp_entry_for (f := func30Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func30 _ initial
    (func30Def.toLocals [.i64 (UInt64.ofNat n), .i64 (UInt64.ofNat index),
      .i64 (boolWord axis), .i64 (boolWord forward)]) env
  have hOne : UInt64.ofNat 1 = 1 := rfl
  unfold func30
  cases forward with
  | false =>
    by_cases hz : coordinate = 0
    · cases axis <;>
        simp only [coordinate, stride, Bool.false_eq_true, reduceIte, hOne] at *
      all_goals unfold boolWord; neighbor_peel
      all_goals simp [Traversal.neighborIndex, hz]
    · have hb := hBack hz
      have hbWord : ¬ UInt64.ofNat index < UInt64.ofNat stride := by
        rw [hLower]
        omega
      have hSubtract := hSub hb
      have hNotLess := Nat.not_lt.mpr hb
      cases axis <;>
        simp only [coordinate, stride, Bool.false_eq_true, reduceIte, hOne] at *
      all_goals unfold boolWord; neighbor_peel
      all_goals simp [Traversal.neighborIndex, hz, hNotLess]
  | true =>
    by_cases hf : coordinate + 1 < n <;> cases axis <;>
      simp only [coordinate, stride, Bool.false_eq_true, reduceIte, hOne] at *
    all_goals unfold boolWord; neighbor_peel
    all_goals simp [Traversal.neighborIndex, hf]

#print axioms neighborIndex_exact

end Project.EulerRiemann.Execution
