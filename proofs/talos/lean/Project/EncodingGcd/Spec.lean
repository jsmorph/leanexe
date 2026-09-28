import Project.EncodingGcd.Frame
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

namespace Project.EncodingGcd.Spec

open Wasm

def GcdSpecFor (m : Wasm.Module) : Prop :=
  ∀ (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64),
    TerminatesWith env m 0 initial [.i64 b, .i64 a]
      (fun _ result => result = [.i64 (UInt64.ofNat (Nat.gcd a.toNat b.toNat))])

set_option maxHeartbeats 8000000 in
theorem gcd_correct : GcdSpecFor Project.EncodingGcd.«module» := by
  intro env initial a b
  apply TerminatesWith.of_wp_entry (f := Project.EncodingGcd.func0Def) rfl
  intro initial'
  unfold Project.EncodingGcd.func0Def Project.EncodingGcd.func0
  wp_run
  apply wp_block_cons
  apply wp_loop_cons (Inv := loopInvariant initial' a b) (μ := measure)
  · refine ⟨rfl, a, b, a, b, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
      rfl, rfl⟩
  · rintro st s ⟨rfl, l2, l3, x, y, l6, l7, l8, l9, l10, l11, l12, l13,
      l14, l15, l16, l17, l18, l19, l20, l21, l22, rfl, hgcd⟩
    wp_run
    simp [frame]
    by_cases hy : y = 0
    · subst y
      simp [measure, Nat.gcd_zero_right] at hgcd ⊢
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      try wp_peel
      try simp_all [frame, measure]
      exact gcd_zero_value hgcd
    · have hypos : 0 < y.toNat := by
        u64_omega at hy ⊢
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy]
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy, measure]
      try wp_peel
      try simp [hy, measure]

      refine ⟨?_, ?_⟩
      · refine ⟨rfl, l2, l3, y, x % y, x, y, x % y, y, x % y, y, x % y,
          l13, l14, l15, x, y, 0, y, x % y, l21, l22, rfl, ?_⟩
        exact (gcd_step x y).trans hgcd
      · simpa only [UInt64.toNat_mod] using remainder_lt x y hy

theorem gcd_zero_right (env : HostEnv Unit) (initial : Store Unit) (a : UInt64) :
    TerminatesWith env Project.EncodingGcd.«module» 0 initial [.i64 0, .i64 a]
      (fun _ result => result = [.i64 a]) := by
  simpa using gcd_correct env initial a 0

theorem gcd_symmetric (env : HostEnv Unit) (initial : Store Unit) (a b : UInt64) :
    TerminatesWith env Project.EncodingGcd.«module» 0 initial [.i64 b, .i64 a]
      (fun _ result => result = [.i64 (UInt64.ofNat (Nat.gcd b.toNat a.toNat))]) := by
  simpa only [Nat.gcd_comm a.toNat b.toNat] using gcd_correct env initial a b

end Project.EncodingGcd.Spec
