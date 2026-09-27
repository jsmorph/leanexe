import Project.PairFree.Program
import Project.Common
import Project.Runtime.Spec
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop
import Interpreter.Wasm.Wp.Call
import Std.Tactic.BVDecide

/-!
# Shared definitions for the `sharedPairFreeStats` proof

The allocation-size functions, the raw free and decrement theorems for the
release function, and the copy-loop frame, invariant, and measure.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

macro "wp_run_big" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

/-- The rounded allocation size for a payload of `n` bytes. -/
def allocSize (n : Nat) : Nat :=
  (n + 7) / 8 * 8

def allocSizeU (len : UInt64) : UInt64 :=
  (len + 1 + 7) / 8 * 8

/-- Releasing a nonzero raw object with refcount one puts it at the head of
the free list: the refcount slot is cleared, the next-pointer slot receives
the old free-list head, global 1 points at the object, and the release and
free counters advance. -/
theorem func7_frees_fresh_raw (env : HostEnv Unit) (st4 : Store Unit)
    (p g1v c4 c5 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st4.mem.read64 ((p - 40).toUInt32) = 1)
    (hkind : st4.mem.read64 ((p - 24).toUInt32) = 0)
    (hg1 : st4.globals.globals[1]? = some (.i64 g1v))
    (hg4 : st4.globals.globals[4]? = some (.i64 c4))
    (hg5 : st4.globals.globals[5]? = some (.i64 c5)) :
    TerminatesWith (m := «module») (id := 7) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = (st4.mem.write64 ((p - 40).toUInt32) 0).write64
          ((p - 8).toUInt32) g1v ∧
        st'.globals.globals =
          ((st4.globals.globals.set 4 (.i64 (c4 + 1))).set 5
            (.i64 (c5 + 1))).set 1 (.i64 p)) :=
  Project.Runtime.release_frees_fresh_raw env «module» 7 st4 p g1v c4 c5
    (by rfl) rfl hp48 hp32 hfit hmagic hrc hkind hg1 hg4 hg5

/-- Releasing an object whose refcount exceeds one decrements it and
returns: one store, one counter, nothing else. -/
theorem func7_decrements (env : HostEnv Unit) (st4 : Store Unit)
    (p c c4 : UInt64)
    (hp48 : 48 ≤ p.toNat)
    (hp32 : p.toNat < 4294967296)
    (hfit : p.toNat ≤ st4.mem.pages * 65536)
    (hmagic : st4.mem.read64 ((p - 48).toUInt32) = 5501223100278326855)
    (hrc : st4.mem.read64 ((p - 40).toUInt32) = c)
    (hc1 : 1 < c.toNat)
    (hg4 : st4.globals.globals[4]? = some (.i64 c4)) :
    TerminatesWith (m := «module») (id := 7) (initial := st4) (env := env)
      [.i64 p]
      (fun st' vs =>
        vs = [] ∧
        st'.mem = st4.mem.write64 ((p - 40).toUInt32) (c - 1) ∧
        st'.globals.globals =
          st4.globals.globals.set 4 (.i64 (c4 + 1))) :=
  Project.Runtime.release_decrements env «module» 7 st4 p c c4 (by rfl) rfl
    hp48 hp32 hfit hmagic hrc hc1 hg4

def vFrame
    (p0 ptr len l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19
      l20 l21 l22 l23 l24 : UInt64) : Locals :=
  { params := [.i64 p0, .i64 ptr, .i64 len],
    locals := [.i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7, .i64 l8, .i64 l9,
      .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15, .i64 l16,
      .i64 l17, .i64 l18, .i64 l19, .i64 l20, .i64 l21, .i64 l22, .i64 l23,
      .i64 l24],
    values := [] }

/-- Copy-loop invariant for the temporary: as in the push proofs, plus the
byte-array header facts the later phases read back. -/
def vInv (st0 : Store Unit) (ptr g0 g2 : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ bytes.length ∧
      s = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k) (allocSizeU (UInt64.ofNat bytes.length)) 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48) ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        ((st0.globals.globals.set 0
          (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
          (.i64 (g2 + 1))) ∧
      (∀ a : Nat, a < g0.toNat → st.mem.bytes a = st0.mem.bytes a) ∧
      (∀ i : Nat, i < k → st.mem.bytes (g0.toNat + 48 + i) = bytes[i]!) ∧
      st.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
        5501223100278326855 ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
        allocSizeU (UInt64.ofNat bytes.length) ∧
      st.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0

def vMeasure (bytes : List UInt8) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ ::
      _ :: .i64 l18 :: _ =>
      bytes.length - l18.toNat
  | _ => 0

end Project.PairFree.Spec
