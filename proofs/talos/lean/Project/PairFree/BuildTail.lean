import Project.PairFree.AllocationTail

/-!
# Pair construction tail

The post-loop suffix allocates the pair array, fills its cells, and updates the
shared child.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576
theorem buildsTail (env : HostEnv Unit) (st1 st2 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hg1 : st1.globals.globals[1]? = some (.i64 0))
    (hg2 : st1.globals.globals[2]? = some (.i64 g2))
    (hg3 : st1.globals.globals[3]? = some (.i64 g3))
    (hg4 : st1.globals.globals[4]? = some (.i64 g4))
    (hg5 : st1.globals.globals[5]? = some (.i64 g5))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16)
    (hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24)
    (hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32)
    (hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40)
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hglen : 3 < st1.globals.globals.length)
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh24 : st2.mem.read64
      (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0)
    (POST : Assertion Unit)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hDone : ∀ (st' : Store Unit) (s' : Locals),
      pairBuildResult st1 ptr g0 g2 g3 g4 g5 bytes st' s' →
      POST (.Fallthrough st' s')) :
    wp «module» pairBuildTail POST
      { st2 with mem := (st2.mem.write8
        (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296)) 33) }
      (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
        (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
        0) env := by
  rw [pairBuild_split]
  simp only [pairBuildHead, pairBuildTail, pairAfterProg, List.take,
    List.drop]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  set stB : Store Unit := { st2 with mem := (st2.mem.write8
    (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
    33) } with hstB
  have PB := buildsStB env st1 st2 stB ptr g0 g2 g3 g4 g5 bytes hLen
    hPtr32 hBelow hFit32 hg0_32 hlenU hszU hszN_ge hszN_ge8 hFit hPages
    hg1 hg2 hg3 hg4 hg5 hpg hgl hh0 hh8 hh24 hsub40 hsub32 hsub24 hsub16
    hsub8 hglen hstB
  change wp «module» pairAllocationBody _ stB _ env
  change wp «module» pairAllocationBody _ stB
    (vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr
      (UInt64.ofNat bytes.length) 0 (g0 + 48) (g0 + 48)
      (UInt64.ofNat bytes.length + 1) 0 0 0 ptr
      (UInt64.ofNat bytes.length) 33 (g0 + 48)
      (UInt64.ofNat bytes.length + 1) (UInt64.ofNat bytes.length) 56 0 0
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
      ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
      0) env
  change wp «module» pairAllocationPrelude _ stB _ env
  have hAllocation := pairAllocationPrelude_correct env stB st1 ptr g0 g2
    g3 g4 g5 bytes
    hFit32 hFit hPages hlenU hszU hszN_ge hszN_ge8 hg0_32 h17 hsub40
    PB.1 PB.2.1 PB.2.2.2.2.2.1 PB.2.2.2.2.2.2.1
    PB.2.2.2.2.2.2.2.1 PB.2.2.2.2.2.2.2.2.2.2.1 PB.2.2.1
    PB.2.2.2.1 PB.2.2.2.2.2.2.2.2.2.2.2.1
    PB.2.2.2.2.2.2.2.2.2.2.2.2.1 PB.2.2.2.2.2.2.2.2.1
    PB.2.2.2.2.2.2.2.2.2.2.2.2.2
    PB.2.2.2.2.2.2.2.2.2.1 POST hTrap hDone
  refine wp.conseq ?_ hAllocation
  intro cont h
  cases cont with
  | Fallthrough st' s' =>
    simpa only [pairBuildContinuation] using h
  | Break k st' s' =>
    cases k with
    | zero => simpa only [pairBuildContinuation] using h
    | succ k => simpa only [pairBuildContinuation] using h
  | Return st' values =>
    simpa only [pairBuildContinuation] using h
  | Trap st' message =>
    simpa only [pairBuildContinuation] using h
  | Invalid message =>
    simpa only [pairBuildContinuation] using h
  | OutOfFuel =>
    simpa only [pairBuildContinuation] using h
  | ReturnCall id st' values =>
    simpa only [pairBuildContinuation] using h
  | Throwing tag args st' s' =>
    simpa only [pairBuildContinuation] using h

end Project.PairFree.Spec
