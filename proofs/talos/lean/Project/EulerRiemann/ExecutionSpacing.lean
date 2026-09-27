import Project.EulerRiemann.ExecutionTimeGuard

namespace Project.EulerRiemann.Execution
open Wasm

macro "small_natural_finish" : tactic => `(tactic|
  (repeat
    first
    | wp_run [func33Def, List.set, List.getElem?_cons_zero, List.getElem?_cons_succ,
        reduceIte, Nat.reduceAdd, Nat.reduceLT, Nat.reduceSub, *]
    | (try simp only [Wasm.wp_iff_control_types])
      refine wp_iff_cons rfl ?_
      conv => arg 2; simp [*, -UInt64.ofNat_add, -UInt64.not_le])
  <;> simp [Time.smallNaturalBits, Nat.toUInt64_eq, *])

set_option maxHeartbeats 400000 in
theorem smallNaturalBits_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerRiemann.«module» 33 initial [.i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.smallNaturalBits n)]) := by
  have hnNat := UInt64.toNat_ofNat_of_lt'
    (show n < UInt64.size by change n < 18446744073709551616; omega)
  have hLt (bound : UInt64) : (UInt64.ofNat n < bound) ↔ n < bound.toNat := by
    rw [UInt64.lt_iff_toNat_lt, hnNat]
  have hZero : (UInt64.ofNat n = 0) ↔ n = 0 := by
    constructor
    · intro h
      have := congrArg UInt64.toNat h
      simpa only [hnNat, UInt64.toNat_zero] using this
    · intro h
      subst n
      rfl
  refine TerminatesWith.of_wp_entry_for (f := func33Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func33 _ initial
    (func33Def.toLocals [.i64 (UInt64.ofNat n)]) env
  unfold func33
  by_cases hz : n = 0
  · small_natural_finish
  by_cases h2 : n < 2
  · small_natural_finish
  by_cases h4 : n < 4
  · small_natural_finish
  by_cases h8 : n < 8
  · small_natural_finish
  by_cases h16 : n < 16
  · small_natural_finish
  by_cases h32 : n < 32
  · small_natural_finish
  by_cases h64 : n < 64
  · small_natural_finish
  by_cases h128 : n < 128
  · small_natural_finish
  by_cases h256 : n < 256
  · small_natural_finish
  by_cases h512 : n < 512 <;> small_natural_finish

theorem spacing_exact (env : HostEnv Unit) (initial : Store Unit)
    (n : Nat) (hn : n ≤ 800) :
    TerminatesWith env Project.EulerRiemann.«module» 34 initial [.i64 (UInt64.ofNat n)]
      (fun final values => final = initial ∧ values = [.i64 (Time.spacing n)]) := by
  refine TerminatesWith.of_wp_entry_for (f := func34Def) rfl ?_ (by decide)
  change wp Project.EulerRiemann.«module» func34 _ initial
    (func34Def.toLocals [.i64 (UInt64.ofNat n)]) env
  unfold func34
  wp_run [func34Def, List.set, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub]
  refine wp_call_tw ((smallNaturalBits_exact env initial n hn).append_args rfl rfl rfl
    [.f64 4607182418800017408]) ?_
  rintro current values ⟨out, rfl, hCurrent, rfl⟩
  subst current
  wp_run [func34Def, List.set, Nat.reduceLT, Nat.reduceAdd, Nat.reduceSub]
  simp [Time.spacing, f64Div]

#print axioms smallNaturalBits_exact
#print axioms spacing_exact

end Project.EulerRiemann.Execution
