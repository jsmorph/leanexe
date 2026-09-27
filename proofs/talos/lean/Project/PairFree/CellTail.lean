import Project.PairFree.RetainTail

/-!
# Pair-cell construction

This module starts after allocation has written the pair-array header and
array length.  The theorem fills both cells and transfers control to the
retain branch.  The boundary gives every cell store a concrete frame and
memory address.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

def pairCellTail : Wasm.Program := pairBuildTail.drop 14

def pairHeaderTail : Wasm.Program :=
  (pairBuildTail.drop 4).take 10 ++ pairCellTail

def pairHeaderMem (stB : Store Unit) (g0 : UInt64)
    (bytes : List UInt8) : Mem :=
  ((((((stB.mem.write64
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
      4294967296)) 1)

def pairHeaderStore (stB : Store Unit) (g0 : UInt64)
    (bytes : List UInt8) : Store Unit :=
  { stB with
    globals := { globals := (stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56))) },
    mem := pairHeaderMem stB g0 bytes }

def pairCellMem (stB : Store Unit) (g0 : UInt64)
    (bytes : List UInt8) : Mem :=
  (pairHeaderMem stB g0 bytes).write64
    (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) 2

def pairCellStore (stB : Store Unit) (g0 g2 : UInt64)
    (bytes : List UInt8) : Store Unit :=
  { stB with
    globals := { globals := (stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (.i64 (g2 + 1 + 1)) },
    mem := pairCellMem stB g0 bytes }

def pairHeaderFrame (ptr g0 : UInt64) (bytes : List UInt8) : Locals :=
  vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
    (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
    (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
    (UInt64.ofNat bytes.length) 33 (g0 + 48)
    (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)
    ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) /
      65536 + 1)
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)

theorem pairCellTail_correct (env : HostEnv Unit) (stB st1 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hg0_32 : g0.toNat < 4294967296)
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hpgB : stB.mem.pages = st1.mem.pages)
    (h0B : 0 < stB.globals.globals.length)
    (h2B : 2 < stB.globals.globals.length)
    (h3B : 3 < stB.globals.globals.length)
    (hg1B : stB.globals.globals[1]? = some (.i64 0))
    (hg2B : stB.globals.globals[2]? = some (.i64 (g2 + 1)))
    (hg3C : ((stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (.i64 (g2 + 1 + 1)))[3]? = some (.i64 g3))
    (hg4B : stB.globals.globals[4]? = some (.i64 g4))
    (hg5B : stB.globals.globals[5]? = some (.i64 g5))
    (hh0B : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8B : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh24B : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0)
    (POST : Assertion Unit)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hDone : ∀ (st' : Store Unit) (s' : Locals),
      pairBuildResult st1 ptr g0 g2 g3 g4 g5 bytes st' s' →
      POST (.Fallthrough st' s')) :
    wp «module» pairCellTail POST (pairCellStore stB g0 g2 bytes)
      (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) /
          65536 + 1)
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)) env := by
  simp only [pairCellTail, pairBuildTail, pairAfterProg, List.drop,
    pairCellStore]
  have PC := buildsCells _ stB g0 bytes hFit32 hszU hszN_ge hszN_ge8
    hg0_32 hh0B hh8B rfl
  have hCellBound (k : Nat) (hk : 8 ≤ k) (hk' : k ≤ 48) :
      ¬ (pairCellMem stB g0 bytes).pages * 65536 <
        (g0.toNat + 48 +
          (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + k) %
          4294967296 + 8 := by
    simp only [pairCellMem, pairHeaderMem, Mem.write64_pages]
    rw [Nat.mod_eq_of_lt (by omega), hpgB]
    omega
  have hb8 := hCellBound 8 (by omega) (by omega)
  have hb16 := hCellBound 16 (by omega) (by omega)
  have hb24 := hCellBound 24 (by omega) (by omega)
  have hb32 := hCellBound 32 (by omega) (by omega)
  have hb40 := hCellBound 40 (by omega) (by omega)
  have hb48 := hCellBound 48 (by omega) (by omega)
  wp_run_folded [hb8, hb16, hb24, hb32, hb40, hb48]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  simp only [pairCellMem, pairHeaderMem] at hb8 hb16 hb24 hb32 hb40 hb48
  simp only [pairCellMem, pairHeaderMem, PC.1]
  simp only [hb8, hb16, hb24, hb32, hb40, hb48, if_false]
  exact pairRetainBranch_correct env stB st1 ptr g0 g2 g3 g4 g5 bytes
    hFit32 hFit hszU hg0_32 hsub40 hpgB h0B h2B h3B hg1B hg3C hg4B
    hg5B hh0B hh24B PC.2.1 PC.2.2 POST hTrap hDone

theorem pairHeaderTail_correct (env : HostEnv Unit) (stB st1 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hg0_32 : g0.toNat < 4294967296)
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hpgB : stB.mem.pages = st1.mem.pages)
    (h0B : 0 < stB.globals.globals.length)
    (h2B : 2 < stB.globals.globals.length)
    (h3B : 3 < stB.globals.globals.length)
    (hg1B : stB.globals.globals[1]? = some (.i64 0))
    (hg2B : stB.globals.globals[2]? = some (.i64 (g2 + 1)))
    (hg3C : ((stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (.i64 (g2 + 1 + 1)))[3]? = some (.i64 g3))
    (hg4B : stB.globals.globals[4]? = some (.i64 g4))
    (hg5B : stB.globals.globals[5]? = some (.i64 g5))
    (hh0B : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8B : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh24B : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0)
    (POST : Assertion Unit)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hDone : ∀ (st' : Store Unit) (s' : Locals),
      pairBuildResult st1 ptr g0 g2 g3 g4 g5 bytes st' s' →
      POST (.Fallthrough st' s')) :
    wp «module» pairHeaderTail POST (pairHeaderStore stB g0 bytes)
      (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) /
          65536 + 1)
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)) env := by
  simp only [pairHeaderTail, pairBuildTail, pairAfterProg, List.drop,
    List.take, pairHeaderStore]
  have hg2H : (stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56)))[2]? = some (.i64 (g2 + 1)) := by
    rw [List.getElem?_set]
    simp only [if_neg (by omega : ¬ (0 = 2))]
    exact hg2B
  have hb0 : ¬ (pairHeaderMem stB g0 bytes).pages * 65536 <
      (g0.toNat + 48 +
        (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) %
        4294967296 + 8 := by
    simp only [pairHeaderMem, Mem.write64_pages]
    rw [Nat.mod_eq_of_lt (by omega), hpgB]
    omega
  wp_run_folded [hg2H, hb0]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  simp only [pairHeaderMem] at hb0
  simp only [pairHeaderMem]
  refine ⟨Nat.le_of_not_gt hb0, ?_⟩
  exact pairCellTail_correct env stB st1 ptr g0 g2 g3 g4 g5 bytes hFit32
    hFit hPages hlenU hszU hszN_ge hszN_ge8 hg0_32 h17 hsub40 hpgB h0B
    h2B h3B hg1B hg2B hg3C hg4B hg5B hh0B hh8B hh24B POST hTrap hDone

end Project.PairFree.Spec
