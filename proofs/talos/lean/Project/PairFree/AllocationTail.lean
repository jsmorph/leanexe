import Project.PairFree.CellTail

/-!
# Pair-header writes

This module isolates the six stores at the end of the pair-array allocation
branch.  The theorem starts after allocation arithmetic has updated the heap
pointer and transfers control to the header-to-cell theorem.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

def pairAllocationBody : Wasm.Program :=
  match pairBuildTail.drop 3 with
  | .iff _ _ body _ _ _ :: _ => body
  | _ => []

def pairHeaderWrites : Wasm.Program :=
  pairAllocationBody.drop 28

def pairAllocationPrelude : Wasm.Program :=
  pairAllocationBody

def pairBuildHead : Wasm.Program :=
  pairBuildTail.take 4

def pairBuildRest : Wasm.Program :=
  pairBuildTail.drop 4

theorem pairBuild_split : pairBuildTail = pairBuildHead ++ pairBuildRest := by
  simp only [pairBuildHead, pairBuildRest, List.take_append_drop]

def pairBuildContinuation (env : HostEnv Unit) (POST : Assertion Unit) :
    Assertion Unit :=
  fun cont =>
    match cont with
    | .Fallthrough st' s' =>
      wp «module» pairBuildRest POST st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } env
    | .Break 0 st' s' =>
      wp «module» pairBuildRest POST st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } env
    | .Break (Nat.succ k) st' s' => POST (.Break k st' s')
    | other => POST other

def pairHeaderWriteStore (stB : Store Unit) (g0 : UInt64)
    (bytes : List UInt8) : Store Unit :=
  { stB with
    globals := { globals := (stB.globals.globals.set 0
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))) } }

theorem pairHeaderWrites_correct (env : HostEnv Unit) (stB st1 : Store Unit)
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
    wp «module» pairHeaderWrites (pairBuildContinuation env POST)
      (pairHeaderWriteStore stB g0 bytes)
      (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) /
          65536 + 1)
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)) env := by
  simp only [pairHeaderWrites, pairAllocationBody, pairBuildTail,
    pairAfterProg, List.drop, pairHeaderWriteStore]
  have PA := buildsArith st1 g0 bytes hFit32 h17 hsub40 hg0_32 hlenU hszU
    hszN_ge hszN_ge8 hFit hPages
  wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  rw [PA.2.2.2.2.2.2.2.2.2.1, PA.2.2.2.2.2.2.2.2.2.2.1,
    PA.2.2.2.2.2.2.2.2.2.2.2.1, PA.2.2.2.2.2.2.2.2.2.2.2.2.1,
    PA.2.2.2.2.2.2.2.2.2.2.2.2.2.1]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_⟩
  exact pairHeaderTail_correct env stB st1 ptr g0 g2 g3 g4 g5 bytes
    hFit32 hFit hPages hlenU hszU hszN_ge hszN_ge8 hg0_32 h17 hsub40
    hpgB h0B h2B h3B hg1B hg2B hg3C hg4B hg5B hh0B hh8B hh24B POST
    hTrap hDone

theorem pairAllocationPrelude_correct (env : HostEnv Unit)
    (stB st1 : Store Unit) (ptr g0 g2 g3 g4 g5 : UInt64)
    (bytes : List UInt8)
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
    (hg0B : stB.globals.globals[0]? = some
      (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))))
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
    wp «module» pairAllocationPrelude (pairBuildContinuation env POST) stB
      (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
      0) env := by
  rw [show pairAllocationPrelude =
      pairAllocationBody.take 28 ++ pairHeaderWrites from by
    simp only [pairAllocationPrelude, pairHeaderWrites,
      List.take_append_drop]]
  simp only [pairAllocationBody, pairBuildTail,
    pairAfterProg, List.drop, List.take]
  have PA := buildsArith st1 g0 bytes hFit32 h17 hsub40 hg0_32 hlenU hszU
    hszN_ge hszN_ge8 hFit hPages
  have hPageCast : (UInt32.ofNat st1.mem.pages).toUInt64 =
      UInt64.ofNat (st1.mem.pages % 4294967296) := by
    apply UInt64.toNat.inj
    rw [PA.2.2.2.2.2.2.1,
      toNat_ofNat_lt (by rw [size_eq]; omega),
      Nat.mod_eq_of_lt (by omega)]
  wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp only [hg0B]
  try wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [PA.2.2.1])]
  wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  try simp only [hpgB]
  try wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  refine wp_iff_cons rfl ?_
  rw [if_neg (by rw [hPageCast]; simp [PA.2.2.2.2.2.2.2.1])]
  wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp only [hg0B]
  try wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  try simp only [hg0B]
  try wp_run_folded [pairBuildContinuation]
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  exact pairHeaderWrites_correct env stB st1 ptr g0 g2 g3 g4 g5 bytes
    hFit32 hFit hPages hlenU hszU hszN_ge hszN_ge8 hg0_32 h17 hsub40
    hpgB h0B h2B h3B hg1B hg2B hg3C hg4B hg5B hh0B hh8B hh24B POST
    hTrap hDone

end Project.PairFree.Spec
