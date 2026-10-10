import Verified.Reflect.Command
import Examples.Drone.Costs
import Examples.Drone.Extend
import Examples.Drone.Flat
import Examples.Drone.WholeFlight

/-! The thirty-first program of the verified compiler: the drone planner of
`Examples/Drone/Program.lean`, compiled unchanged.  The planner finds the flight of least duration
over up to 64 stations of terrain, with the altitude above the floors as the second criterion,
among 45 states per station, and returns the altitude and speed at each station.  The program
lists `floorAt` and `best`, which `LeanExe` inlines, as functions, and the reflector reflects the
named constants `stateCount`, `infinity`, and `unreachable` as their values.  `Choice` is
represented as its three words by the instance of `Examples/Drone/Flat.lean`.  The compiler's
theorem states that the module computes `compute`, or traps at `unreachable`, which it allows on
any input since an allocation traps when memory runs out.  With the planner's own theorems,
`compute_correct` and `compute_safe`, which concern the Lean definition, `drone_compute` and
`drone_safe` state that the module's results are optimal and safe flights.  `compute_bound` bounds
the allocations of `compute` by 2,251,064 bytes from `compiled.compute.bound_eq`, and
`drone_trapFree` states that the module computes `compute` without a trap whenever `top` can rise
by that much within the memory's cap. -/

namespace Verified.Examples.Drone

open _root_.Examples.Drone

verified_compile compiled := [distance, altitude, speed, floorAt, ceilSqrt, restSeconds,
  edgeTicks, choose, predecessor, best, advance, initial, validHeights, extend, forward, output,
  compute]

open _root_.Examples.Drone.Output _root_.Examples.Drone.Planner
  _root_.Examples.Drone.Forward in
/-- The bytes of `compiled.module` decode to the module, whose entry 18 computes `compute`: a call
with a terrain returns the words of `compute` or traps at `unreachable`.  For valid terrain those
words are an admitted flight from rest on the ground at the first station to rest on the ground at
the last, and no admitted flight costs less.  For empty or invalid terrain they are `#[]`. -/
theorem drone_compute : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA true compiled.module 18 compute (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) ∧
    (∀ terrain, terrainBound terrain → 0 < terrain.size →
      let r := floors terrain
      let stop := stops terrain.size.toUInt64
      let n := terrain.size - 1
      (compute terrain).size = 2 * terrain.size ∧
      Encoded r stop n 0 (rowCost (layers r stop n) 0) (compute terrain).toList ∧
      ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other) ∧
    (∀ terrain, terrain.size < 2 ^ 64 → ¬(terrainBound terrain ∧ 0 < terrain.size) →
      compute terrain = #[]) := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.compute.implements,
    fun terrain h hn => compute_correct terrain h hn,
    fun terrain hs h => compute_invalid terrain hs h⟩

open _root_.Examples.Drone.Output in
/-- The bytes of `compiled.module` decode to the module, whose entry 18 computes `compute`, and for
valid nonempty terrain the flight that `compute` returns is safe: the clearance, speed, and
acceleration limits hold throughout the point-mass trajectory that its words define. -/
theorem drone_safe : ∃ bytes, Wasm.Encoding.encode compiled.module = .ok bytes ∧
    Wasm.Encoding.decode bytes = .ok compiled.module ∧
    LeanExe.Pipeline.ImplementsA true compiled.module 18 compute (fun _ _ _ => True)
      (fun _ _ _ _ _ => True) ∧
    ∀ terrain, terrainBound terrain → 0 < terrain.size → WholeFlight.Safe terrain := by
  obtain ⟨bytes, success, decoded, _⟩ := compiled.bytes
  exact ⟨bytes, success, decoded, compiled.compute.implements,
    fun terrain h hn => WholeFlight.compute_safe terrain h hn⟩

/-- The bound of `compute` is at most 2,251,064 bytes for every terrain: `forward` builds at most
63 tables, the `k`-th of `45 (k + 2)` choices of three words, after the first row of 45 choices,
and `output` builds at most 128 words. -/
theorem compute_bound (terrain : Array UInt64) : compiled.compute.bound terrain ≤ 2251064 := by
  rw [compiled.compute.bound_eq, compiled.forward.bound_eq, compiled.initial.bound_eq,
    compiled.output.bound_eq]
  generalize hc : (if (decide (0 < terrain.size.toUInt64) && decide (terrain.size.toUInt64 ≤ 64) &&
      validHeights terrain) = true then terrain.size.toUInt64 else 0) = c
  have hc64 : c.toNat ≤ 64 := by
    subst hc
    split
    · next h =>
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact UInt64.le_iff_toNat_le.mp h.1.2
    · simp
  refine Nat.le_trans (Nat.add_le_add (Nat.add_le_add_left (loopCost_le
    (fun k (s : UInt64 × UInt64 × Array Choice) =>
      (s.1 = 0 ∧ s.2.1.toNat = k + 1 ∧ s.2.2.size = 45 * (k + 1) ∧ k + 1 ≤ 64) ∨ s.1 = 1)
    (fun k => if k + 1 < c.toNat then 1080 * (k + 2) + 56 else 0) ?hcost ?hstep ?hI) _)
    (Nat.le_refl _)) ?_
  case hcost =>
    rintro k ⟨status, i, table⟩ (⟨h0, hi, hs, hk⟩ | h1)
    · simp only at h0 hi hs hk
      subst h0
      simp only [beq_self_eq_true, ↓reduceIte, Nat.zero_add]
      rw [compiled.extend.bound_eq]
      have hlt : i < c ↔ k + 1 < c.toNat := by rw [UInt64.lt_iff_toNat_lt, hi]
      by_cases h : i < c
      · rw [ite_eq_left h, ite_eq_left (hlt.mp h)]
        have hsz : (table.size.toUInt64 + stateCount).toNat = 45 * (k + 2) := by
          rw [UInt64.toNat_add, Nat.toUInt64_eq, UInt64.toNat_ofNat', hs]
          have : c.toNat ≤ 64 := hc64
          simp only [stateCount, UInt64.reduceToNat]
          omega
        rw [hsz, blockCost_eq]
        omega
      · rw [ite_eq_right h]
        exact Nat.zero_le _
    · simp only at h1
      subst h1
      simp
  case hstep =>
    rintro k ⟨status, i, table⟩ (⟨h0, hi, hs, hk⟩ | h1) hC
    · simp only at h0 hi hs hk
      subst h0
      show (_ ∧ _ ∧ _ ∧ _) ∨ _
      dsimp only
      by_cases h : i < c
      · rw [extend_lt terrain c i table h]
        have hik : k + 1 < c.toNat := by rw [UInt64.lt_iff_toNat_lt, hi] at h; exact h
        left
        refine ⟨rfl, ?_, ?_, by omega⟩
        · rw [UInt64.toNat_add, hi]; simp only [UInt64.reduceToNat]; omega
        · have := extend_size terrain c i table h (by omega)
          rw [extend_lt terrain c i table h] at this
          rw [this, hs]; omega
      · rw [extend_ge terrain c i table h]
        right; rfl
    · simp only at h1 hC
      subst h1
      simp at hC
  case hI =>
    left
    refine ⟨rfl, rfl, ?_, by omega⟩
    rw [initial_build, LeanExe.IR.build_size]
    rfl
  -- The sum, at most its value for 64 stations, and the first and last rows.
  have hsum : sumBelow (fun k => if k + 1 < c.toNat then 1080 * (k + 2) + 56 else 0)
      (UInt64.toNat 64) ≤ 2248848 :=
    (sumBelow_le fun k _ => by split <;> split <;> omega).trans
      (show sumBelow (fun k => if k + 1 < 64 then 1080 * (k + 2) + 56 else 0) 64 ≤ 2248848 by
        decide)
  have hout : (2 * c).toNat ≤ 128 := by
    rw [UInt64.toNat_mul]; simp only [UInt64.reduceToNat]; omega
  simp only [blockCost_eq, stateCount, UInt64.reduceToNat] at hsum ⊢
  omega

/-- The bytes of `compiled.module` decode to the module, whose entry 18 computes `compute` without
a trap whenever `top` can rise by 2,251,064 bytes within the memory's cap, and raises `top` by at
most that much. -/
theorem drone_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 18 (fun x => compute x)
    (fun _ heap store => heap.Within store compiled.module 2251064)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 2251064) :=
  compiled.compute.trapFree.mono (fun x _ _ h => h.mono (compute_bound x))
    fun x _ _ _ _ _ h => h.trans (Nat.add_le_add_left (compute_bound x) _)

end Verified.Examples.Drone
