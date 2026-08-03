import Project.PairFree.BuildCore

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

def pairRetainTail : Wasm.Program := pairBuildTail.drop 98

def pairCellsMem (stB : Store Unit) (g0 : UInt64)
    (bytes : List UInt8) : Mem :=
  (((((((((((((stB.mem.write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296))
    5501223100278326855).write64
    (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) %
      4294967296)) 1).write64
    (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 32) %
      4294967296)) 56).write64
    (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) %
      4294967296)) 2).write64
    (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) %
      4294967296)) 3).write64
    (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) %
      4294967296)) 1).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296))
    2).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) %
      4294967296)) (g0 + 48)).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) %
      4294967296)) (g0 + 48)).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) %
      4294967296)) (UInt64.ofNat bytes.length + 1)).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) %
      4294967296)) (g0 + 48)).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) %
      4294967296)) (g0 + 48)).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) %
      4294967296)) (UInt64.ofNat bytes.length + 1))

def pairCellsStore (stB : Store Unit) (g0 g2 : UInt64)
    (bytes : List UInt8) : Store Unit :=
  { stB with
    globals := { globals := (stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (.i64 (g2 + 1 + 1)) },
    mem := pairCellsMem stB g0 bytes }

def pairRetainBranch : Wasm.Program := pairBuildTail.drop 113

def pairRetainFrame (ptr g0 : UInt64) (bytes : List UInt8) : Locals :=
  { vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
      (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
      (UInt64.ofNat bytes.length + 1) 0 0 0
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)
      (g0 + 48) 33 (g0 + 48) (g0 + 48)
      (UInt64.ofNat bytes.length + 1) 56 0 0
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)
      ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) /
        65536 + 1)
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48) with
    values := [.i32 (if g0 + 48 = 0 then 0 else 1)] }

theorem pairRetainBranch_correct (env : HostEnv Unit) (stB st1 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hg0_32 : g0.toNat < 4294967296)
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hpgB : stB.mem.pages = st1.mem.pages)
    (h0B : 0 < stB.globals.globals.length)
    (h2B : 2 < stB.globals.globals.length)
    (h3B : 3 < stB.globals.globals.length)
    (hg1B : stB.globals.globals[1]? = some (.i64 0))
    (hg3C : ((stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (.i64 (g2 + 1 + 1)))[3]? = some (.i64 g3))
    (hg4B : stB.globals.globals[4]? = some (.i64 g4))
    (hg5B : stB.globals.globals[5]? = some (.i64 g5))
    (hh0B : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh24B : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0)
    (hmagic : (pairCellsMem stB g0 bytes).read64
      (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855)
    (hrc : (pairCellsMem stB g0 bytes).read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (POST : Assertion Unit)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hDone : ∀ (st' : Store Unit) (s' : Locals),
      pairBuildResult st1 ptr g0 g2 g3 g4 g5 bytes st' s' →
      POST (.Fallthrough st' s')) :
    wp «module» pairRetainBranch POST (pairCellsStore stB g0 g2 bytes)
      (pairRetainFrame ptr g0 bytes) env := by
  simp only [pairRetainBranch, pairBuildTail, pairAfterProg, List.drop,
    pairCellsStore, pairRetainFrame]
  have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
    u64_omega
  have hg048 : g0 + 48 ≠ 0 := by
    u64_omega
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp [hg048])]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  try simp only [hsub48, hmagic]
  try wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  refine ⟨?_, ?_⟩
  · simp only [pairCellsMem, Mem.write64_pages]
    rw [Nat.mod_eq_of_lt hg0_32, hpgB]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp)]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  refine ⟨?_, ?_⟩
  · simp only [pairCellsMem, Mem.write64_pages]
    rw [hsub40, Nat.mod_eq_of_lt (by omega), hpgB]
    omega
  have hrc' := hrc
  rw [show (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) =
      (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) from by
    rw [hsub40]] at hrc'
  rw [hrc']
  try wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by decide)]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp only [hg3C]
  try wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  refine ⟨?_, ?_⟩
  · simp only [pairCellsMem, Mem.write64_pages]
    rw [hsub40, Nat.mod_eq_of_lt (by omega), hpgB]
    omega
  refine hDone _ _ ?_
  simp only [pairBuildResult]
  have P := buildsFinal _ stB st1 ptr g0 g2 g3 g4 g5 bytes
    rfl hFit32 hszU hg0_32 hsub40 hpgB h0B h2B h3B hg1B hg4B hg5B
    hh0B hh24B
  simpa [pairCellsMem, h0B, h2B, h3B] using P

end Project.PairFree.Spec
