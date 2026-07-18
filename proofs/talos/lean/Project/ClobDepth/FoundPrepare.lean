import Project.ClobDepth.MissingBranch

/-!
# Found-price preparation

The found branch decodes the scan index, reads the matching quantity, adds the
incoming quantity, reloads the level count, and checks the index bound.
-/

namespace Project.ClobDepth.FoundPrepare

open Wasm Project.Common Project.ClobDepth Project.ClobDepth.Model
  Project.ClobDepth.Properties Project.ClobDepth.Representation

def branchFrame (owner source price qty : UInt64) (levels : List LevelL)
    (i : Nat) : Locals :=
  { Scan.outcomeFrame owner source price qty (UInt64.ofNat levels.length)
      (UInt64.ofNat i) (UInt64.ofNat i + 1) levels[i]!.lprice
      levels[i]!.lqty 0 with values := [] }

def prepareFrame (owner source price qty : UInt64) (levels : List LevelL)
    (i : Nat) : Locals :=
  { params := [.i64 owner, .i64 source, .i64 price, .i64 qty]
    locals := [.i64 levels[i]!.lprice, .i64 levels[i]!.lqty,
      .i64 (UInt64.ofNat i + 1), .i64 0, .i64 0, .i64 source,
      .i64 (UInt64.ofNat i), .i64 0, .i64 0, .i64 0, .i64 source,
      .i64 (UInt64.ofNat i), .i64 (UInt64.ofNat levels.length),
      .i64 (UInt64.ofNat i + 1), .i64 0, .i64 0, .i64 price,
      .i64 (levels[i]!.lqty + qty), .i64 0, .i64 0, .i64 source,
      .i64 (UInt64.ofNat i), .i64 (UInt64.ofNat i + 1), .i64 1, .i64 0,
      .i64 0]
    values := [.i32 1] }

set_option maxRecDepth 1048576
set_option maxHeartbeats 8000000

set_option Elab.async false in
theorem foundPrepareProg_spec
    (env : HostEnv Unit) (st : Store Unit)
    (owner source price qty : UInt64) (levels : List LevelL) (i : Nat)
    (hLength : levels.length < 4294967296)
    (hIndex : priceIdx levels price = some i)
    (hLevels : LevelsAt st source levels)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp «module» rest Q st
      (prepareFrame owner source price qty levels i) env) :
    wp «module» (Entry.foundPrepareProg ++ rest) Q st
      (branchFrame owner source price qty levels i) env := by
  have hi : i < levels.length := priceIdx_some_lt hIndex
  have hiU : (UInt64.ofNat i).toNat = i := by u64_omega
  have hLengthU : (UInt64.ofNat levels.length).toNat = levels.length := by u64_omega
  have hEncoded : UInt64.ofNat i + 1 ≠ 0 := by
    intro hZero
    have hZeroNat := congrArg UInt64.toNat hZero
    rw [toNat_add_one (by rw [hiU, size_eq]; omega), hiU] at hZeroNat
    simp at hZeroNat
  have hIndexLt : UInt64.ofNat i < UInt64.ofNat levels.length := by
    rw [UInt64.lt_iff_toNat_lt, hiU, hLengthU]
    exact hi
  have hQtyRead := (hLevels.2 i hi).2.1
  have hQtyBound := (hLevels.2 i hi).2.2
  simp only [Entry.foundPrepareProg, List.cons_append, List.nil_append]
  simp [branchFrame, Scan.outcomeFrame]
  rw [if_neg hEncoded]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg hEncoded]
  rw [if_neg (by simp)]
  wp_run
  try simp
  rw [if_neg hEncoded]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run
  try simp
  refine wp_iff_cons rfl ?_
  rw [if_neg hEncoded]
  rw [if_neg (by simp)]
  wp_run
  try simp
  rw [if_neg (Nat.not_lt.mpr hLevels.1.2), hLevels.1.1]
  rw [if_pos hIndexLt]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  wp_run
  try simp
  rw [if_neg (Nat.not_lt.mpr hQtyBound), hQtyRead]
  rw [if_neg (Nat.not_lt.mpr hLevels.1.2), hLevels.1.1]
  rw [if_pos hIndexLt]
  simpa [prepareFrame] using hNext

end Project.ClobDepth.FoundPrepare
