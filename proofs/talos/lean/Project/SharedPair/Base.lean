import Project.SharedPair.Program
import Project.Common
import Project.Runtime.Spec
import Interpreter.Wasm.Wp.Tactic
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Specification for `sharedPushPair`

The export builds `input ++ [33]` once and returns the two-element array
`#[appended, appended]`.  The literal transfers ownership of the temporary at
its first element and retains it at the second, so the returned structure
holds two references backed by a refcount of exactly two.  The theorem runs
from any store whose free list is empty and whose heap top leaves room for
both allocations: the array cells alias the single temporary, the retain
counter advances by one, the alloc counter by two, and everything below the
old heap top is unchanged.  This is the first proof of the inline retain
sequence the compiler emits for shared children.
-/

namespace Project.SharedPair.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

/-- The rounded allocation size for a payload of `n` bytes. -/
macro "wp_run_big" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

def allocSize (n : Nat) : Nat :=
  (n + 7) / 8 * 8

def allocSizeU (len : UInt64) : UInt64 :=
  (len + 1 + 7) / 8 * 8

def vFrame
    (ptr len l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19
      l20 l21 l22 : UInt64) : Locals :=
  { params := [.i64 ptr, .i64 len],
    locals := [.i64 l2, .i64 l3, .i64 l4, .i64 l5, .i64 l6, .i64 l7, .i64 l8,
      .i64 l9, .i64 l10, .i64 l11, .i64 l12, .i64 l13, .i64 l14, .i64 l15,
      .i64 l16, .i64 l17, .i64 l18, .i64 l19, .i64 l20, .i64 l21, .i64 l22],
    values := [] }

/-- Copy-loop invariant for the temporary: as in the push proofs, plus the
byte-array header facts the later phases read back. -/
def vInv (st0 : Store Unit) (ptr g0 g2 : UInt64) (bytes : List UInt8) :
    AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ bytes.length ∧
      s = vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
        (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr
        (UInt64.ofNat bytes.length) 33 (g0 + 48)
        (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k)
        (allocSizeU (UInt64.ofNat bytes.length)) 0 0
        (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
        ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
        (g0 + 48) ∧
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
      .i64 l16 :: _ =>
      bytes.length - l16.toNat
  | _ => 0

/-- The generated export builds the temporary, then the pair array whose two
elements alias it, and retains the shared child once. -/
@[spec_of "lean" "LeanExe.Examples.ByteArrayPrograms.sharedPushPair"]
def SharedPairSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr g0 g2 g3 : UInt64)
    (bytes : List UInt8),
    bytes.length + 1 < 4294967296 →
    ptr.toNat + bytes.length < 4294967296 →
    ptr.toNat + bytes.length ≤ g0.toNat →
    g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296 →
    g0.toNat + 152 + allocSize (bytes.length + 1) ≤ st.mem.pages * 65536 →
    st.mem.pages ≤ 65536 →
    st.globals.globals[0]? = some (.i64 g0) →
    st.globals.globals[1]? = some (.i64 0) →
    st.globals.globals[2]? = some (.i64 g2) →
    st.globals.globals[3]? = some (.i64 g3) →
    BytesAt st ptr bytes →
    TerminatesWith (m := «module») (id := 0) (initial := st) (env := env)
      [.i64 (UInt64.ofNat bytes.length), .i64 ptr]
      (fun st' vs =>
        vs = [.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)] ∧
        st'.globals.globals[0]? =
          some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
            56)) ∧
        st'.globals.globals[1]? = some (.i64 0) ∧
        st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
        st'.globals.globals[3]? = some (.i64 (g3 + 1)) ∧
        st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 2 ∧
        (∀ i : Nat, i < bytes.length + 1 →
          st'.mem.bytes (g0.toNat + 48 + i) = (bytes ++ [33])[i]!) ∧
        (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st.mem.bytes a))


def copyResult (st1 : Store Unit) (g0 g2 g3 : UInt64)
    (bytes : List UInt8) (st' : Store Unit) (vs : List Value) : Prop :=
  vs = [.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)] ∧
  st'.globals.globals[0]? =
    some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)) ∧
  st'.globals.globals[1]? = some (.i64 0) ∧
  st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
  st'.globals.globals[3]? = some (.i64 (g3 + 1)) ∧
  st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 2 ∧
  (∀ i : Nat, i < bytes.length + 1 →
    st'.mem.bytes (g0.toNat + 48 + i) = (bytes ++ [33])[i]!) ∧
  (∀ a : Nat, a < g0.toNat → st'.mem.bytes a = st1.mem.bytes a)

def copyPost (st1 : Store Unit) (ptr g0 g2 g3 : UInt64)
    (bytes : List UInt8) : Assertion Unit
  | .Fallthrough st' s' =>
      copyResult st1 g0 g2 g3 bytes st'
        (List.take func0Def.results.length s'.values ++
          List.drop func0Def.params.length
            [.i64 (UInt64.ofNat bytes.length), .i64 ptr])
  | .Return st' vs =>
      copyResult st1 g0 g2 g3 bytes st'
        (List.take func0Def.results.length vs ++
          List.drop func0Def.params.length
            [.i64 (UInt64.ofNat bytes.length), .i64 ptr])
  | _ => False

def copyStore (st1 : Store Unit) (g0 g2 : UInt64)
    (bytes : List UInt8) : Store Unit :=
  { st1 with
    globals :=
      { globals :=
          (st1.globals.globals.set 0
            (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
            (.i64 (g2 + 1)) },
    mem :=
      (((((st1.mem.write64
        (UInt32.ofNat (g0.toNat % 4294967296)) 5501223100278326855).write64
        (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) 1).write64
        (UInt32.ofNat ((g0.toNat + 16) % 4294967296))
          (allocSizeU (UInt64.ofNat bytes.length))).write64
        (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) 0).write64
        (UInt32.ofNat ((g0.toNat + 32) % 4294967296)) 0).write64
        (UInt32.ofNat ((g0.toNat + 40) % 4294967296)) 0 }

def copyLocals (ptr g0 : UInt64) (bytes : List UInt8) : Locals :=
  vFrame ptr (UInt64.ofNat bytes.length) 33 ptr
    (UInt64.ofNat bytes.length) 0 0 0 0 0 0 ptr
    (UInt64.ofNat bytes.length) 33 (g0 + 48)
    (UInt64.ofNat bytes.length + 1) 0
    (allocSizeU (UInt64.ofNat bytes.length)) 0 0
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))
    ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1)
    (g0 + 48)

def copySuffix : Wasm.Program :=
  Project.SharedPair.func0.drop 47

def copyExitProg : Wasm.Program :=
  copySuffix.drop 1

def copyBuildTail : Wasm.Program :=
  Project.SharedPair.func0.drop 88

end Project.SharedPair.Spec
