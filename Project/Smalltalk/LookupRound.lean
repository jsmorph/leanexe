import Project.Smalltalk.LookupScan

namespace Project.Smalltalk.LookupRound
open LeanExe.Smalltalk.Arena LeanExe.Smalltalk.Runtime Project.Smalltalk.Memory
open Project.Smalltalk.LookupStep Project.Smalltalk.LookupSpec

theorem next_existing_scanning {p : Array UInt64} {owner selector index result : UInt64}
    (within : index < read p 1) (existing : result ≠ 0) :
    next p selector (owner, index, result) = (owner, index + 1, result) := by
  have different : index ≠ read p 1 := by intro same; rw [same] at within; exact UInt64.lt_irrefl _ within
  simp only [next, show (result != 0) = true from bne_iff_ne.mpr existing, Bool.true_or, ite_true,
    show (index == read p 1) = false from beq_eq_false_iff_ne.mpr different, Bool.false_eq_true, ite_false]

theorem increment (start : Nat) : start.toUInt64 + 1 = (start + 1).toUInt64 := by
  change UInt64.ofNat start + 1 = UInt64.ofNat (start + 1)
  rw [UInt64.ofNat_add]
  rfl

theorem within_word {p : Array UInt64} {start : Nat} (bound : (read p 1).toNat ≤ 1048576)
    (within : start < (read p 1).toNat) : start.toUInt64 < read p 1 := by
  apply UInt64.lt_iff_toNat_lt.mpr
  rw [UInt64.toNat_ofNat_of_lt' (by change start < 18446744073709551616; omega)]
  exact within

theorem existing_scan {p : Array UInt64} {owner selector result : UInt64}
    (bound : (read p 1).toNat ≤ 1048576) (existing : result ≠ 0)
    (start fuel : Nat) (room : start + fuel ≤ (read p 1).toNat) :
    Loops.applyN (next p selector) fuel (owner, start.toUInt64, result) =
      (owner, (start + fuel).toUInt64, result) := by
  induction fuel generalizing start with
  | zero => simp only [Loops.applyN, Nat.add_zero]
  | succ fuel ih =>
    have within := within_word bound (show start < (read p 1).toNat by omega)
    rw [Loops.applyN, next_existing_scanning within existing, increment, ih (start + 1) (by omega)]
    have same : start + 1 + fuel = start + (fuel + 1) := by omega
    rw [same]

theorem fresh_scan {p : Array UInt64} {owner selector : UInt64}
    (bound : (read p 1).toNat ≤ 1048576) (start fuel : Nat) (room : start + fuel ≤ (read p 1).toNat) :
    Loops.applyN (next p selector) fuel (owner, start.toUInt64, 0) =
      (owner, (start + fuel).toUInt64, own p owner selector start fuel) := by
  induction fuel generalizing start with
  | zero => simp only [Loops.applyN, Nat.add_zero, own]
  | succ fuel ih =>
    have within := within_word bound (show start < (read p 1).toNat by omega)
    have natural : start.toUInt64.toNat = start := UInt64.toNat_ofNat_of_lt' (by change start < 18446744073709551616; omega)
    rw [Loops.applyN, LookupScan.next_scanning within, natural, increment]
    by_cases selected : candidate p owner selector (start + 1) = true
    · simp only [selected, ite_true, own]
      have nonzero : (start + 1).toUInt64 ≠ (0 : UInt64) := by
        intro zero
        have positive := congrArg UInt64.toNat zero
        rw [UInt64.toNat_ofNat_of_lt' (by change start + 1 < 18446744073709551616; omega)] at positive
        change start + 1 = 0 at positive
        omega
      rw [existing_scan bound nonzero (start + 1) fuel (by omega)]
      have same : start + 1 + fuel = start + (fuel + 1) := by omega
      rw [same]
    · simp only [selected, Bool.false_eq_true, ite_false, own]
      rw [ih (start + 1) (by omega)]
      have same : start + 1 + fuel = start + (fuel + 1) := by omega
      rw [same]

theorem round {p : Array UInt64} (bound : (read p 1).toNat ≤ 1048576) (owner selector : UInt64) :
    Loops.applyN (next p selector) ((read p 1).toNat + 1) (owner, 0, 0) =
      (if own p owner selector 0 (read p 1).toNat != 0 || owner == 0 then owner else classAt p owner 0,
        0, own p owner selector 0 (read p 1).toNat) := by
  have scan := fresh_scan (p := p) (owner := owner) (selector := selector) bound 0 (read p 1).toNat (by omega)
  simp only [Nat.zero_add, show (0 : Nat).toUInt64 = (0 : UInt64) from rfl, UInt64.ofNat_toNat] at scan
  rw [Loops.applyN_add, scan, Loops.applyN, Loops.applyN, LookupScan.next_end]

end Project.Smalltalk.LookupRound
