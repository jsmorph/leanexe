import Project.EulerCertificate.SolverScalars
import Project.EulerCertificate.Boundary
import Project.ProofKit.CheckedNatMulArithmetic

namespace Project.EulerCertificate.Execution
open Wasm
open Project.EulerRiemann
open Project.EulerRiemann.Traversal (Cell)
open Project.EulerRiemann.Execution (stateValues boolWord)
open Project.Euler2DCellStep.Sweep (orient)

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

macro "boundary_padded_peel" : tactic => `(tactic|
  repeat
    first
    | wp_run [func162Def, stateValues, boolWord,
        Memory.cellWords, Array.getD, List.set, List.cons_append, List.nil_append,
        UInt64.add_zero, UInt64.zero_add, UInt64.mul_zero, UInt64.zero_mul,
        ← Project.ProofKit.Memory.toUInt32_eq_ofNat, UInt32.add_zero, UInt32.toNat_zero,
        Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, Nat.reducePow, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_mul, -UInt64.ofNat_add, -UInt64.not_le])

theorem boundary_padded_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (axis : Bool) (owner pointer : UInt64)
    (grid : Array Cell) (line k : Nat)
    (hn : 2 ≤ n ∧ n ≤ 800) (hSize : grid.size = n * n)
    (hl : line < n) (hk : k ≤ n + 3) (hGrid : Memory.GridAt initial pointer grid) :
    TerminatesWith env Project.EulerCertificate.«module» 162 initial
      [.i64 (UInt64.ofNat k), .i64 (UInt64.ofNat line), .i64 pointer, .i64 owner,
        .i64 (boolWord axis), .i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧
        values = stateValues (Boundary.padded n axis grid line k)) := by
  let coordinate := min (k - 2) (n - 1)
  let index := if axis then coordinate * n + line else line * n + coordinate
  have hc : coordinate < n := by dsimp [coordinate]; omega
  have hSquare : n * n ≤ 640000 := by nlinarith [hn.2]
  have hNat (a : Nat) (ha : a ≤ 640000) : (UInt64.ofNat a).toNat = a :=
    UInt64.toNat_ofNat_of_lt' (by change a < 18446744073709551616; omega)
  have hnNat := hNat n (by omega)
  have hkNat := hNat k (by omega)
  have hnPredNat := hNat (n - 1) (by omega)
  have hkSubNat := hNat (k - 2) (by omega)
  have hnWord : UInt64.ofNat n ≠ 0 := by
    intro h
    have := congrArg UInt64.toNat h
    simp only [hnNat, UInt64.toNat_zero] at this
    omega
  have hnLower : ¬ UInt64.ofNat n < 1 := by
    simp only [UInt64.lt_iff_toNat_lt, hnNat, UInt64.toNat_one]
    omega
  have hnSub : UInt64.ofNat n - 1 = UInt64.ofNat (n - 1) :=
    (UInt64.ofNat_sub (show 1 ≤ n by omega)).symm
  have hkLower : (UInt64.ofNat k < 2) ↔ k < 2 := by
    simp only [UInt64.lt_iff_toNat_lt, hkNat]
    rfl
  have hkSubtract (h : 2 ≤ k) : UInt64.ofNat k - 2 = UInt64.ofNat (k - 2) :=
    (UInt64.ofNat_sub h).symm
  have hClamp : (UInt64.ofNat (k - 2) ≤ UInt64.ofNat (n - 1)) ↔ k - 2 ≤ n - 1 := by
    simp only [UInt64.le_iff_toNat_le, hkSubNat, hnPredNat]
  have hIndex (a b : Nat) (ha : a < n) (hb : b < n) : a * n + b < grid.size := by
    rw [hSize]
    nlinarith [Nat.mul_le_mul_right n (show a + 1 ≤ n by omega)]
  have hi : index < grid.size := by
    cases axis <;> simp only [index, Bool.false_eq_true, reduceIte]
    · exact hIndex line coordinate hl hc
    · exact hIndex coordinate line hc hl
  have hMulGuard (a : Nat) (ha : a < n) : ¬ (-1 : UInt64) / UInt64.ofNat n < UInt64.ofNat a := by
    apply Project.ProofKit.CheckedNatMul.guard_of_fits _ _ _ hnWord
    rw [hnNat, hNat a (by omega)]
    have : a * n < 640000 := lt_of_lt_of_le (hIndex a 0 ha (by omega)) (by omega)
    change a * n < 18446744073709551616
    omega
  have hMul (a : Nat) : UInt64.ofNat a * UInt64.ofNat n = UInt64.ofNat (a * n) :=
    (UInt64.ofNat_mul a n).symm
  have hAdd (a b : Nat) : UInt64.ofNat (a * n) + UInt64.ofNat b =
      UInt64.ofNat (a * n + b) := (UInt64.ofNat_add (a * n) b).symm
  have hAddGuard (a b : Nat) (ha : a < n) (hb : b < n) :
      ¬ UInt64.ofNat (a * n + b) < UInt64.ofNat (a * n) := by
    have hib := hIndex a b ha hb
    have hs : a * n + b ≤ 640000 := by omega
    simp only [UInt64.lt_iff_toNat_lt, hNat _ hs, hNat _ (show a * n ≤ 640000 by omega)]
    omega
  have hMulLine := hMulGuard line hl
  have hMulCoordinate := hMulGuard coordinate hc
  have hAddLine := hAddGuard line coordinate hl hc
  have hAddCoordinate := hAddGuard coordinate line hc hl
  have hWord : ¬ UInt64.ofNat (n * n) ≤ UInt64.ofNat index := by
    simp only [UInt64.le_iff_toNat_le, hNat (n * n) hSquare, hNat index (by omega)]
    omega
  have hLength := hGrid.lengthRead
  have hLengthBound := Nat.not_lt.mpr hGrid.lengthBound
  have hOffset1 : (UInt64.ofNat index * 7 + 2) * 8 =
      UInt64.ofNat (8 * (7 * index + 1 + 1)) := Memory.field_offset index 1
  have hBound1 := Nat.not_lt.mpr (hGrid.fieldBound index 1 hi (by decide))
  have hRead1 := hGrid.fieldRead index 1 hi (by decide)
  have hOffset2 : (UInt64.ofNat index * 7 + 3) * 8 =
      UInt64.ofNat (8 * (7 * index + 2 + 1)) := Memory.field_offset index 2
  have hBound2 := Nat.not_lt.mpr (hGrid.fieldBound index 2 hi (by decide))
  have hRead2 := hGrid.fieldRead index 2 hi (by decide)
  have hOffset3 : (UInt64.ofNat index * 7 + 4) * 8 =
      UInt64.ofNat (8 * (7 * index + 3 + 1)) := Memory.field_offset index 3
  have hBound3 := Nat.not_lt.mpr (hGrid.fieldBound index 3 hi (by decide))
  have hRead3 := hGrid.fieldRead index 3 hi (by decide)
  have hOffset4 : (UInt64.ofNat index * 7 + 5) * 8 =
      UInt64.ofNat (8 * (7 * index + 4 + 1)) := Memory.field_offset index 4
  have hBound4 := Nat.not_lt.mpr (hGrid.fieldBound index 4 hi (by decide))
  have hRead4 := hGrid.fieldRead index 4 hi (by decide)
  have hGet : grid[index]! = grid[index] := getElem!_pos grid index hi
  refine TerminatesWith.of_wp_entry_for (f := func162Def) rfl ?_ (by decide)
  change wp Project.EulerCertificate.«module» func162 _ initial
    (func162Def.toLocals [.i64 (UInt64.ofNat n), .i64 (boolWord axis),
      .i64 owner, .i64 pointer, .i64 (UInt64.ofNat line), .i64 (UInt64.ofNat k)]) env
  unfold func162
  simp only [Boundary.padded]
  by_cases hSmall : k < 2
  · have hkZero : k - 2 = 0 := by omega
    cases axis <;> simp only [index, coordinate, hkZero, Nat.zero_min,
      Nat.add_zero, Nat.zero_mul, Nat.zero_add,
      Bool.false_eq_true, reduceIte] at *
    all_goals boundary_padded_peel
    all_goals simp [orient]
  · have hkSub := hkSubtract (by omega)
    by_cases hMin : k - 2 ≤ n - 1
    · cases axis <;> simp only [index, coordinate, Nat.min_eq_left hMin,
        Bool.false_eq_true, reduceIte] at *
      all_goals boundary_padded_peel
      all_goals simp [orient]
    · have hMin' : n - 1 ≤ k - 2 := by omega
      cases axis <;> simp only [index, coordinate, Nat.min_eq_right hMin',
        Bool.false_eq_true, reduceIte] at *
      all_goals boundary_padded_peel
      all_goals simp [orient]

#print axioms boundary_padded_exact
end Project.EulerCertificate.Execution
