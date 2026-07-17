import Project.ClobDepth.Entry
import Project.ClobDepth.Properties
import Project.ClobDepth.Representation
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Depth price scan

The generated scan records zero for a missing price and the first matching
index plus one otherwise.  The found outcome retains the loaded price and
quantity for the replacement branch.
-/

namespace Project.ClobDepth.Scan

open Wasm Project.Common Project.ClobDepth Project.ClobDepth.Model
  Project.ClobDepth.Properties Project.ClobDepth.Representation

set_option maxHeartbeats 64000000
set_option maxRecDepth 100000

def entryFrame (owner ptr price qty : UInt64) : Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 price, .i64 qty]
    locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0]
    values := [] }

def loopFrame (owner ptr price qty length cursor encoded f4 f5 : UInt64) :
    Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 price, .i64 qty]
    locals := [.i64 f4, .i64 f5, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 ptr, .i64 length,
      .i64 cursor, .i64 encoded, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0]
    values := [] }

def outcomeFrame (owner ptr price qty length cursor encoded f4 f5 : UInt64)
    (condition : UInt32) : Locals :=
  { params := [.i64 owner, .i64 ptr, .i64 price, .i64 qty]
    locals := [.i64 f4, .i64 f5, .i64 encoded, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 ptr, .i64 length,
      .i64 cursor, .i64 encoded, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 0]
    values := [.i32 condition] }

theorem scanLoop_spec {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program}
    {owner ptr price qty : UInt64} (levels : List LevelL)
    (hLength : levels.length < 4294967296)
    (hLevels : LevelsAt st ptr levels)
    (hNone : priceIdx levels price = none →
      ∀ f4 f5 : UInt64,
        wp «module» rest Q st
          (loopFrame owner ptr price qty (UInt64.ofNat levels.length)
            (UInt64.ofNat levels.length) 0 f4 f5) env)
    (hSome : ∀ i : Nat, priceIdx levels price = some i →
      wp «module» rest Q st
        (loopFrame owner ptr price qty (UInt64.ofNat levels.length)
          (UInt64.ofNat i) (UInt64.ofNat i + 1)
          levels[i]!.lprice levels[i]!.lqty) env) :
    wp «module» (Entry.scanLoopProg ++ rest) Q st
      (loopFrame owner ptr price qty (UInt64.ofNat levels.length) 0 0 0 0)
      env := by
  obtain ⟨-, hElems⟩ := hLevels
  have hLengthU : (UInt64.ofNat levels.length).toNat = levels.length :=
    toNat_ofNat_lt (by rw [size_eq]; omega)
  unfold Entry.scanLoopProg Entry.scanProg Project.ClobDepth.func3
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st' s =>
      st' = st ∧
      ∃ k : Nat, k ≤ levels.length ∧
      (∀ j : Nat, j < k → (levels[j]!.lprice == price) = false) ∧
      ∃ f4 f5 : UInt64,
        s = loopFrame owner ptr price qty (UInt64.ofNat levels.length)
          (UInt64.ofNat k) 0 f4 f5)
    (μ := fun _ s =>
      match s.locals with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
        .i64 cursor :: _ => levels.length - cursor.toNat
      | _ => 0)
  · exact ⟨rfl, 0, Nat.zero_le _, by omega, 0, 0, rfl⟩
  · rintro st2 s2 ⟨rfl, k, hk, hClean, f4, f5, rfl⟩
    have hkU : (UInt64.ofNat k).toNat = k :=
      toNat_ofNat_lt (by rw [size_eq]; omega)
    simp only [loopFrame]
    wp_run
    try simp
    by_cases hEnd : k = levels.length
    · have hge : UInt64.ofNat k ≥ UInt64.ofNat levels.length := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hLengthU]
        omega
      rw [if_pos hge]
      try wp_run
      try simp
      subst k
      exact hNone (priceIdx_none_of_clean levels price hClean) f4 f5
    · have hklt : k < levels.length := Nat.lt_of_le_of_ne hk hEnd
      have hnge : ¬(UInt64.ofNat k ≥ UInt64.ofNat levels.length) := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hLengthU]
        omega
      rw [if_neg hnge]
      wp_run
      try simp
      obtain ⟨⟨hPriceRead, hPriceBound⟩, ⟨hQtyRead, hQtyBound⟩⟩ :=
        hElems k hklt
      rw [if_neg (Nat.not_lt.mpr hPriceBound),
        if_neg (Nat.not_lt.mpr hQtyBound)]
      rw [hPriceRead, hQtyRead]
      by_cases hMatch : (levels[k]!.lprice == price) = true
      · refine wp_iff_cons rfl ?_
        rw [if_pos (by simpa using hMatch)]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_pos (by simp)]
        wp_run
        try simp
        simpa [loopFrame] using
          hSome k (priceIdx_of_first levels price k hklt hClean hMatch)
      · have hMiss : (levels[k]!.lprice == price) = false := by
          simpa using hMatch
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simpa using hMiss)]
        wp_run
        refine wp_iff_cons rfl ?_
        rw [if_neg (by simp)]
        wp_run
        try simp
        have hkAdd : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
            toNat_ofNat_lt (by rw [size_eq]; omega)]
        rw [hkAdd]
        refine ⟨⟨k + 1, by omega, ?_, rfl⟩, by omega⟩
        intro j hj
        by_cases hjk : j < k
        · simpa using hClean j hjk
        · have hjeq : j = k := by omega
          subst j
          simpa using hMiss

theorem scanProg_spec {env : HostEnv Unit} {st : Store Unit}
    {Q : Assertion Unit} {rest : Program}
    {owner ptr price qty : UInt64} (levels : List LevelL)
    (hLength : levels.length < 4294967296)
    (hLevels : LevelsAt st ptr levels)
    (hNone : priceIdx levels price = none →
      ∀ f4 f5 : UInt64,
        wp «module» rest Q st
          (outcomeFrame owner ptr price qty (UInt64.ofNat levels.length)
            (UInt64.ofNat levels.length) 0 f4 f5 1) env)
    (hSome : ∀ i : Nat, priceIdx levels price = some i →
      wp «module» rest Q st
        (outcomeFrame owner ptr price qty (UInt64.ofNat levels.length)
          (UInt64.ofNat i) (UInt64.ofNat i + 1)
          levels[i]!.lprice levels[i]!.lqty 0) env) :
    wp «module» (Entry.scanProg ++ rest) Q st
      (entryFrame owner ptr price qty) env := by
  rw [Entry.scanProg_decomposition]
  simp only [List.append_assoc]
  unfold Entry.scanPrepareProg Entry.scanProg Project.ClobDepth.func3
  simp [entryFrame]
  rw [if_neg (Nat.not_lt.mpr hLevels.1.2), hLevels.1.1]
  apply scanLoop_spec levels hLength hLevels
  · intro hIndex f4 f5
    unfold Entry.scanFinishProg Entry.scanProg Project.ClobDepth.func3
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp)]
    wp_run
    simpa [loopFrame, outcomeFrame] using
      hNone hIndex f4 f5
  · intro i hIndex
    have hi : i < levels.length := priceIdx_some_lt hIndex
    have hiU : (UInt64.ofNat i).toNat = i :=
      toNat_ofNat_lt (by rw [size_eq]; omega)
    have hEncoded : UInt64.ofNat i + 1 ≠ 0 := by
      intro hZero
      have hZeroNat := congrArg UInt64.toNat hZero
      rw [toNat_add_one (by rw [hiU, size_eq]; omega), hiU] at hZeroNat
      simp at hZeroNat
    unfold Entry.scanFinishProg Entry.scanProg Project.ClobDepth.func3
    wp_run
    simp
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simpa using hEncoded)]
    wp_run
    simpa [loopFrame, outcomeFrame] using
      hSome i hIndex

end Project.ClobDepth.Scan
