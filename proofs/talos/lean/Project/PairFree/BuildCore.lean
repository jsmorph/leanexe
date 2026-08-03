import Project.PairFree.Base
import Project.PairFree.Frame
import Project.WpScaffold

/-!
# Construction of the shared pair

The compiled `sharedPushPair` helper builds the temporary, the pair array
aliasing it twice, and retains the shared child once.
-/

namespace Project.PairFree.Spec

open Wasm
open Project.Common

set_option maxHeartbeats 400000000
set_option maxRecDepth 1048576

/-- Every conjunct of the construction's final package after the pair
stores, over a memory bound to the fourteen-write chain by equation.
The closing discharge applies this as one term, so none of these
conjuncts is ever focused as a goal in the loop context. -/
theorem buildsFinal (M : Mem) (stB st1 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (hM : M =
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
          4294967296)) (UInt64.ofNat bytes.length + 1)).write64
        (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) 2)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hg0_32 : g0.toNat < 4294967296)
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hpgB : stB.mem.pages = st1.mem.pages)
    (h0B : 0 < stB.globals.globals.length)
    (h2B : 2 < stB.globals.globals.length)
    (h3B : 3 < stB.globals.globals.length)
    (hg1B : stB.globals.globals[1]? = some (.i64 0))
    (hg4B : stB.globals.globals[4]? = some (.i64 g4))
    (hg5B : stB.globals.globals[5]? = some (.i64 g5))
    (hh0e : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh24e : stB.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) =
      0) :
    (List.take func0Def.results.length
        [Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48),
          Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)] ++
      List.drop func0Def.params.length
        [Value.i64 (UInt64.ofNat bytes.length), Value.i64 ptr, Value.i64 0] =
      [Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48),
        Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)]) ∧
    stB.mem.pages = st1.mem.pages ∧
    (stB.globals.globals.set 0
      (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56)))[0]? =
      some (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56)) ∧
    stB.globals.globals[1]? = some (Value.i64 0) ∧
    ((stB.globals.globals.set 0
      (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (Value.i64 (g2 + 1 + 1)))[2]? =
      some (Value.i64 (g2 + 1 + 1)) ∧
    (((stB.globals.globals.set 0
      (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 +
        56))).set 2 (Value.i64 (g2 + 1 + 1))).set 3
      (Value.i64 (g3 + 1)))[3]? = some (Value.i64 (g3 + 1)) ∧
    stB.globals.globals[4]? = some (Value.i64 g4) ∧
    stB.globals.globals[5]? = some (Value.i64 g5) ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) =
      5501223100278326855 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) -
      40) % 4294967296)) = 1 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) -
      24) % 4294967296)) = 2 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) -
      16) % 4294967296)) = 3 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) -
      8) % 4294967296)) = 1 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) =
      2 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) %
      4294967296)) = g0 + 48 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) %
      4294967296)) = g0 + 48 ∧
    M.read64 (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 2 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0 := by
  subst hM
  have haddr40 : (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) =
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
    rw [hsub40]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · simp [func0Def]
  · exact hpgB
  · simp [h0B]
  · exact hg1B
  · simp [h2B]
  · simp [h3B]
  · exact hg4B
  · exact hg5B
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      hh0e]
  · rw [haddr40, Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
      hh24e]


private theorem buildsNotLe (bytes : List UInt8) (k : Nat)
    (hLen : bytes.length + 1 < 4294967296)
    (hklt : k < bytes.length) :
    ¬ (UInt64.ofNat k ≥ UInt64.ofNat bytes.length) := by
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  have hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length := by
    u64_omega
  rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, hlenU]
  omega

private def pairCopyBody : Wasm.Program :=
  [.localGet 18, .localGet 14, .geUI64, .br_if 1, .localGet 16,
    .localGet 18, .addI64, .wrapI64, .localGet 13,
    .localGet 18, .addI64, .wrapI64, .load8U 0, .store8 0,
    .localGet 18, .constI64 1, .addI64, .localSet 18, .br 0]

/-- The copy-loop body obligation, generic over the loop rule's
postcondition so no continuation appears in any statement.  The
repeat premise takes the re-established invariant and measure
decrease; the exit premise takes the exit state by equation. -/
theorem buildsBody (env : HostEnv Unit) (st1 st2 : Store Unit)
    (ptr g0 g2 : UInt64) (bytes : List UInt8) (k : Nat)
    (POST : Assertion Unit) (m0 : Nat)
    (hLen : bytes.length + 1 < 4294967296)
    (hPtr32 : ptr.toNat + bytes.length < 4294967296)
    (hBelow : ptr.toNat + bytes.length ≤ g0.toNat)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hg0_32 : g0.toNat < 4294967296)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hInput : BytesAt st1 ptr bytes)
    (hk : k ≤ bytes.length)
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hlo : ∀ a < g0.toNat, st2.mem.bytes a = st1.mem.bytes a)
    (hpref : ∀ i < k, st2.mem.bytes (g0.toNat + 48 + i) = bytes[i]!)
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh16 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 16) % 4294967296)) =
      allocSizeU (UInt64.ofNat bytes.length))
    (hh24 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) =
      0)
    (hm0 : bytes.length - k = m0)
    (hTrap : ∀ (st' : Store Unit) (msg : String),
      POST (.Trap st' msg) = False)
    (hRepeat : ∀ (st' : Store Unit) (s' : Locals),
      vInv st1 ptr g0 g2 bytes st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } ∧
      vMeasure bytes st'
        { s' with values := s'.values.take 0 ++ ([] : List Value).drop 0 } <
        m0 →
      POST (.Break 0 st' s'))
    (hExit : ∀ (st' : Store Unit) (s' : Locals),
      k = bytes.length ∧ st' = st2 ∧
      s' = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k) (allocSizeU (UInt64.ofNat bytes.length)) 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48) →
      POST (.Break 1 st' s'))
    (sB : Locals)
    (hsB : sB = vFrame 0 ptr (UInt64.ofNat bytes.length) 33 ptr (UInt64.ofNat bytes.length) 0 0 0 0 0 0 0 ptr (UInt64.ofNat bytes.length) 33 (g0 + 48) (UInt64.ofNat bytes.length + 1) (UInt64.ofNat k) (allocSizeU (UInt64.ofNat bytes.length)) 0 0 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) - 1) / 65536 + 1) (g0 + 48)) :
    wp «module» pairCopyBody POST st2 sB env := by
  subst hsB
  have hkU : (UInt64.ofNat k).toNat = k := by u64_omega
  simp only [pairCopyBody]
  wp_run_folded []
  try simp only [hTrap, if_false, false_and, and_false]
  try simp
  try simp only [hTrap, if_false, false_and, and_false]
  by_cases hkend : k = bytes.length
  swap
  · -- copy one byte and continue
    simp only [if_neg
      (buildsNotLe bytes k hLen (Nat.lt_of_le_of_ne hk hkend))]
    try simp
    try simp only [hTrap, if_false, false_and, and_false]
    have hklt : k < bytes.length := Nat.lt_of_le_of_ne hk hkend
    obtain ⟨hread, hbound⟩ := hInput k hklt
    have hsrcN : (ptr + UInt64.ofNat k).toNat = ptr.toNat + k := by
      rw [UInt64.toNat_add, hkU]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsrc32 : (ptr + UInt64.ofNat k).toUInt32 =
        UInt32.ofNat ((ptr.toNat + k) % 4294967296) := by
      rw [toUInt32_eq_ofNat, hsrcN]
    rw [hsrc32] at hread hbound
    rw [toUInt32_ofNat_mod_toNat] at hbound
    have hkadd : (UInt64.ofNat k + 1) = UInt64.ofNat (k + 1) := by
      apply UInt64.toNat.inj
      rw [toNat_add_one, hkU, toNat_ofNat_lt (by rw [size_eq]; omega)]
      rw [hkU]
      rw [size_eq]
      omega
    have hreadval : st2.mem.read8
        (UInt32.ofNat ((ptr.toNat + k) % 4294967296)) = bytes[k]! := by
      rw [Mem.read8, toUInt32_ofNat_mod_toNat]
      rw [Nat.mod_eq_of_lt (by omega)]
      rw [hlo (ptr.toNat + k) (by omega)]
      have hthis := hread
      rw [Mem.read8, toUInt32_ofNat_mod_toNat,
        Nat.mod_eq_of_lt (by omega)] at hthis
      exact hthis
    rw [hreadval]
    refine ⟨by omega, by omega,
      hRepeat _ _ ⟨⟨k + 1, hklt, ?_, hpg, hgl, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩⟩
    · rw [← hkadd]
      simp [vFrame]
    · intro a ha
      rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
      exact hlo a ha
    · intro i hi
      by_cases hieq : i = k
      · subst hieq
        rw [write8_bytes_hit _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
      · rw [write8_bytes_ne _ _ _ (by rw [toUInt32_ofNat_mod_toNat]; omega)]
        exact hpref i (by omega)
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh0
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh8
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh16
    · rw [read64_write8_ne _ _ _ _
        (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
      exact hh24
    · simp [vMeasure]
      omega

  · -- all bytes copied: take the exit branch
    have hle : (UInt64.ofNat bytes.length) ≤ (UInt64.ofNat k) := by
      rw [UInt64.le_iff_toNat_le, hkU, hlenU]
      omega
    have hge : UInt64.ofNat k ≥ UInt64.ofNat bytes.length := hle
    rw [if_pos hge]
    try simp
    try simp only [hTrap, if_false, false_and, and_false]
    exact hExit _ _ ⟨hkend, rfl, rfl⟩

def pairAfterProg : Wasm.Program :=
  [Instruction.iff 0 0 [Instruction.constI64 8, Instruction.localSet 19] [], Instruction.constI64 0, Instruction.localSet 24, Instruction.constI64 0, Instruction.localSet 20, Instruction.globalGet 1, Instruction.localSet 21, Instruction.block 0 0 [Instruction.loop 0 0 [Instruction.localGet 21, Instruction.constI64 0, Instruction.eqI64, Instruction.br_if 1, Instruction.localGet 24, Instruction.constI64 0, Instruction.neI64, Instruction.br_if 1, Instruction.localGet 21, Instruction.constI64 32, Instruction.subI64, Instruction.wrapI64, Instruction.load64 0, Instruction.localSet 22, Instruction.localGet 21, Instruction.constI64 8, Instruction.subI64, Instruction.wrapI64, Instruction.load64 0, Instruction.localSet 23, Instruction.localGet 22, Instruction.localGet 19, Instruction.geUI64, Instruction.iff 0 0 [Instruction.localGet 20, Instruction.constI64 0, Instruction.eqI64, Instruction.iff 0 0 [Instruction.localGet 23, Instruction.globalSet 1] [Instruction.localGet 20, Instruction.constI64 8, Instruction.subI64, Instruction.wrapI64, Instruction.localGet 23, Instruction.store64 0], Instruction.localGet 21, Instruction.constI64 48, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 5501223100278326855, Instruction.store64 0, Instruction.localGet 21, Instruction.constI64 40, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 1, Instruction.store64 0, Instruction.localGet 21, Instruction.constI64 32, Instruction.subI64, Instruction.wrapI64, Instruction.localGet 22, Instruction.store64 0, Instruction.localGet 21, Instruction.constI64 24, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 2, Instruction.store64 0, Instruction.localGet 21, Instruction.constI64 16, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 3, Instruction.store64 0, Instruction.localGet 21, Instruction.constI64 8, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 1, Instruction.store64 0, Instruction.localGet 21, Instruction.localSet 24] [Instruction.localGet 21, Instruction.localSet 20, Instruction.localGet 23, Instruction.localSet 21], Instruction.br 0]], Instruction.localGet 24, Instruction.constI64 0, Instruction.eqI64, Instruction.iff 0 0 [Instruction.globalGet 0, Instruction.constI64 48, Instruction.addI64, Instruction.localGet 19, Instruction.addI64, Instruction.localSet 22, Instruction.localGet 22, Instruction.globalGet 0, Instruction.ltUI64, Instruction.iff 0 0 [Instruction.unreachable] [], Instruction.localGet 22, Instruction.constI64 1, Instruction.subI64, Instruction.constI64 65536, Instruction.divUI64, Instruction.constI64 1, Instruction.addI64, Instruction.localSet 23, Instruction.memorySize, Instruction.extendUI32, Instruction.localGet 23, Instruction.ltUI64, Instruction.iff 0 0 [Instruction.localGet 23, Instruction.memorySize, Instruction.extendUI32, Instruction.subI64, Instruction.wrapI64, Instruction.memoryGrow, Instruction.const 4294967295, Instruction.eq, Instruction.iff 0 0 [Instruction.unreachable] []] [], Instruction.globalGet 0, Instruction.constI64 48, Instruction.addI64, Instruction.localSet 24, Instruction.localGet 22, Instruction.globalSet 0, Instruction.localGet 24, Instruction.constI64 48, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 5501223100278326855, Instruction.store64 0, Instruction.localGet 24, Instruction.constI64 40, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 1, Instruction.store64 0, Instruction.localGet 24, Instruction.constI64 32, Instruction.subI64, Instruction.wrapI64, Instruction.localGet 19, Instruction.store64 0, Instruction.localGet 24, Instruction.constI64 24, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 2, Instruction.store64 0, Instruction.localGet 24, Instruction.constI64 16, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 3, Instruction.store64 0, Instruction.localGet 24, Instruction.constI64 8, Instruction.subI64, Instruction.wrapI64, Instruction.constI64 1, Instruction.store64 0] [], Instruction.globalGet 2, Instruction.constI64 1, Instruction.addI64, Instruction.globalSet 2, Instruction.localGet 24, Instruction.localSet 13, Instruction.localGet 13, Instruction.wrapI64, Instruction.constI64 2, Instruction.store64 0, Instruction.localGet 7, Instruction.localSet 16, Instruction.localGet 8, Instruction.localSet 17, Instruction.localGet 9, Instruction.localSet 18, Instruction.localGet 13, Instruction.constI64 0, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 1, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.localGet 16, Instruction.store64 0, Instruction.localGet 13, Instruction.constI64 0, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 2, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.localGet 17, Instruction.store64 0, Instruction.localGet 13, Instruction.constI64 0, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 3, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.localGet 18, Instruction.store64 0, Instruction.localGet 7, Instruction.localSet 16, Instruction.localGet 8, Instruction.localSet 17, Instruction.localGet 9, Instruction.localSet 18, Instruction.localGet 13, Instruction.constI64 1, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 1, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.localGet 16, Instruction.store64 0, Instruction.localGet 13, Instruction.constI64 1, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 2, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.localGet 17, Instruction.store64 0, Instruction.localGet 13, Instruction.constI64 1, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 3, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.localGet 18, Instruction.store64 0, Instruction.localGet 13, Instruction.constI64 1, Instruction.constI64 3, Instruction.mulI64, Instruction.constI64 1, Instruction.addI64, Instruction.constI64 8, Instruction.mulI64, Instruction.addI64, Instruction.wrapI64, Instruction.load64 0, Instruction.localSet 14, Instruction.localGet 14, Instruction.constI64 0, Instruction.neI64, Instruction.iff 0 0 [Instruction.localGet 14, Instruction.constI64 48, Instruction.subI64, Instruction.wrapI64, Instruction.load64 0, Instruction.constI64 5501223100278326855, Instruction.neI64, Instruction.iff 0 0 [Instruction.unreachable] [], Instruction.localGet 14, Instruction.constI64 40, Instruction.subI64, Instruction.wrapI64, Instruction.load64 0, Instruction.localSet 15, Instruction.localGet 15, Instruction.constI64 0, Instruction.eqI64, Instruction.iff 0 0 [Instruction.unreachable] [], Instruction.globalGet 3, Instruction.constI64 1, Instruction.addI64, Instruction.globalSet 3, Instruction.localGet 14, Instruction.constI64 40, Instruction.subI64, Instruction.wrapI64, Instruction.localGet 15, Instruction.constI64 1, Instruction.addI64, Instruction.store64 0] [], Instruction.localGet 13, Instruction.localSet 10, Instruction.localGet 10, Instruction.localSet 11, Instruction.localGet 10, Instruction.localSet 12, Instruction.localGet 11, Instruction.localGet 12]

def pairBuildTail : Wasm.Program := pairAfterProg.drop 8

def pairBuildResult (st1 : Store Unit)
    (ptr g0 g2 g3 g4 g5 : UInt64) (bytes : List UInt8)
    (st' : Store Unit) (s' : Locals) : Prop :=
  List.take func0Def.results.length s'.values ++
      List.drop func0Def.params.length
        [Value.i64 (UInt64.ofNat bytes.length), Value.i64 ptr, Value.i64 0] =
      [Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48),
        Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48)] ∧
    st'.mem.pages = st1.mem.pages ∧
    st'.globals.globals[0]? = some (.i64
      (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56)) ∧
    st'.globals.globals[1]? = some (.i64 0) ∧
    st'.globals.globals[2]? = some (.i64 (g2 + 1 + 1)) ∧
    st'.globals.globals[3]? = some (.i64 (g3 + 1)) ∧
    st'.globals.globals[4]? = some (.i64 g4) ∧
    st'.globals.globals[5]? = some (.i64 g5) ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) =
      5501223100278326855 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 +
      allocSize (bytes.length + 1) - 40) % 4294967296)) = 1 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 +
      allocSize (bytes.length + 1) - 24) % 4294967296)) = 2 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 +
      allocSize (bytes.length + 1) - 16) % 4294967296)) = 3 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 96 +
      allocSize (bytes.length + 1) - 8) % 4294967296)) = 1 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) %
      4294967296)) = 2 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) %
      4294967296)) = g0 + 48 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 48 +
      (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) %
      4294967296)) = g0 + 48 ∧
    st'.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 2 ∧
    st'.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0

private theorem buildsMods (g0 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1)) :
    (g0.toNat) % 4294967296 = g0.toNat ∧
    (g0.toNat + 8) % 4294967296 = g0.toNat + 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 ∧
    (g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296 = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    exact Nat.mod_eq_of_lt (by omega)

theorem buildsCells (M : Mem) (stB : Store Unit)
    (g0 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hg0_32 : g0.toNat < 4294967296)
    (hB0 : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hB8 : stB.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hM : M = (((((((((((((stB.mem.write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 4294967296)) 5501223100278326855).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 40) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 32) % 4294967296)) 56).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 24) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 16) % 4294967296)) 3).write64 (UInt32.ofNat ((g0.toNat + 96 + allocSize (bytes.length + 1) - 8) % 4294967296)) 1).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48) % 4294967296)) 2).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 8) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 16) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 24) % 4294967296)) (UInt64.ofNat bytes.length + 1)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 40) % 4294967296)) (g0 + 48)).write64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 48) % 4294967296)) (UInt64.ofNat bytes.length + 1))) :
    M.read64 (UInt32.ofNat ((g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat + 48 + 32) % 4294967296)) = g0 + 48 ∧
    M.read64 (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 ∧
    M.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
  subst hM
  refine ⟨?_, ?_, ?_⟩
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    Mem.read64_write64_same]
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hB0
  · rw [read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega),
    read64_write64_ne _ _ _ _ (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hB8

theorem buildsArith (st1 : Store Unit) (g0 : UInt64) (bytes : List UInt8)
    (hFit32 : g0.toNat + 152 + allocSize (bytes.length + 1) < 4294967296)
    (h17 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)).toNat =
      g0.toNat + 48 + allocSize (bytes.length + 1))
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hg0_32 : g0.toNat < 4294967296)
    (hlenU : (UInt64.ofNat bytes.length).toNat = bytes.length)
    (hszU : (allocSizeU (UInt64.ofNat bytes.length)).toNat =
      allocSize (bytes.length + 1))
    (hszN_ge : bytes.length + 1 ≤ allocSize (bytes.length + 1))
    (hszN_ge8 : 8 ≤ allocSize (bytes.length + 1))
    (hFit : g0.toNat + 152 + allocSize (bytes.length + 1) ≤
      st1.mem.pages * 65536)
    (hPages : st1.mem.pages ≤ 65536) :
    (48 : UInt64).toNat = 48 ∧
    (18446744073709551616 : Nat) = UInt64.size ∧
    ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 < g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) - 1 ∧
    ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1).toNat = (g0.toNat + 152 + allocSize (bytes.length + 1) - 1) / 65536 + 1 ∧
    ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1 ≤ UInt64.ofNat (st1.mem.pages % 4294967296) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 40).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 32).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 24).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 16).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 ∧
    (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 8).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 ∧
    (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 18446744073709551616 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat ∧
    ¬ ((g0 + 48 : UInt64) = 0) ∧
    (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) = (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
  have h48 : (48 : UInt64).toNat = 48 :=
    rfl
  have hs : (18446744073709551616 : Nat) = UInt64.size :=
    rfl
  have hno_wrap2 : ¬ (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 < g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add, h17]
    have ha : (48 : UInt64).toNat = 48 := rfl
    have hb : (56 : UInt64).toNat = 56 := rfl
    rw [ha, hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have h17b : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, h17]
    have ha : (48 : UInt64).toNat = 48 := rfl
    have hb : (56 : UInt64).toNat = 56 := rfl
    rw [ha, hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsub1b : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1).toNat = g0.toNat + 152 + allocSize (bytes.length + 1) - 1 := by
    rw [UInt64.toNat_sub, h17b]
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h1]
    omega
  have hpn2 : ((g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1).toNat = (g0.toNat + 152 + allocSize (bytes.length + 1) - 1) / 65536 + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_div, hsub1b]
    have h65536 : (65536 : UInt64).toNat = 65536 := rfl
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h65536, h1]
    omega
  have hp32b : ((UInt32.ofNat st1.mem.pages).toUInt64).toNat = st1.mem.pages := by
    have hlt : st1.mem.pages < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    have h1 : (UInt32.ofNat st1.mem.pages).toNat = st1.mem.pages :=
      UInt32.toNat_ofNat_of_lt' hlt
    simp [h1]
  have hgeM : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56 - 1) / 65536 + 1 ≤ UInt64.ofNat (st1.mem.pages % 4294967296) := by
    rw [UInt64.le_iff_toNat_le, hpn2,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    omega
  have hB48 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) := by
    rw [UInt64.toNat_add, h17]
    have ha : (48 : UInt64).toNat = 48 := rfl
    rw [ha]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB40 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 40).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 40 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (40 : UInt64).toNat = 40 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB32 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 32).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 32 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (32 : UInt64).toNat = 32 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB24 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 24).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 24 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (24 : UInt64).toNat = 24 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB16 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 16).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 16 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (16 : UInt64).toNat = 16 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hsubB8 : (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 - 8).toNat = g0.toNat + 96 + allocSize (bytes.length + 1) - 8 := by
    rw [UInt64.toNat_sub, hB48]
    have hb : (8 : UInt64).toNat = 8 := rfl
    rw [hb]
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have hXmod : (g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat) % 18446744073709551616 = g0.toNat + 48 + (allocSizeU (UInt64.ofNat bytes.length)).toNat :=
    Nat.mod_eq_of_lt (by omega)
  have hpne : ¬ ((g0 + 48 : UInt64) = 0) := by
    intro h
    have := congrArg UInt64.toNat h
    rw [UInt64.toNat_add] at this
    have hc : (48 : UInt64).toNat = 48 := rfl
    have h0 : (0 : UInt64).toNat = 0 := rfl
    rw [hc, h0] at this
    have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
    omega
  have haddr40 : (UInt32.ofNat ((g0 + 48 - 40).toNat % 4294967296)) = (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) := by
    rw [hsub40]
  exact ⟨h48, hs, hno_wrap2, h17b, hsub1b, hpn2, hp32b, hgeM, hB48, hsubB40, hsubB32, hsubB24, hsubB16, hsubB8, hXmod, hpne, haddr40⟩

theorem buildsStB (env : HostEnv Unit) (st1 st2 stB : Store Unit)
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
    (hpg : st2.mem.pages = st1.mem.pages)
    (hgl : st2.globals.globals =
      (st1.globals.globals.set 0
        (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length)))).set 2
        (.i64 (g2 + 1)))
    (hh0 : st2.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) =
      5501223100278326855)
    (hh8 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1)
    (hh24 : st2.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) =
      0)
    (hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8)
    (hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16)
    (hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24)
    (hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32)
    (hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40)
    (hglen : 3 < st1.globals.globals.length)
    (hstB : stB = { st2 with mem := (st2.mem.write8
      (UInt32.ofNat ((g0.toNat + 48 + bytes.length) % 4294967296))
      33) }) :
    stB.globals.globals[0]? = some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) ∧
    stB.mem.pages = st1.mem.pages ∧
    stB.globals.globals[2]? = some (.i64 (g2 + 1)) ∧
    ((stB.globals.globals.set 0 (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56))).set 2 (Value.i64 (g2 + 1 + 1)))[3]? = some (Value.i64 g3) ∧
    stB.globals.globals.length = st1.globals.globals.length ∧
    0 < stB.globals.globals.length ∧
    2 < stB.globals.globals.length ∧
    3 < stB.globals.globals.length ∧
    stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 ∧
    stB.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0 ∧
    stB.globals.globals[1]? = some (.i64 0) ∧
    stB.globals.globals[4]? = some (.i64 g4) ∧
    stB.globals.globals[5]? = some (.i64 g5) ∧
    stB.mem.read64 (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
  have hg0len : 0 < st1.globals.globals.length := by omega
  have hg1len : 1 < st1.globals.globals.length := by omega
  have hg2len : 2 < st1.globals.globals.length := by omega
  have hgnil : ¬ st1.globals.globals = [] := by
    intro h
    rw [h] at hglen
    simp at hglen
  have hh0e : stB.mem.read64 (UInt32.ofNat (g0.toNat % 4294967296)) = 5501223100278326855 := by
    rw [hstB]
    dsimp only
    rw [read64_write8_ne _ _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hh0
  have hh8e : stB.mem.read64
      (UInt32.ofNat ((g0.toNat + 8) % 4294967296)) = 1 := by
    rw [hstB]
    dsimp only
    rw [read64_write8_ne _ _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hh8
  have hg0S : stB.globals.globals[0]? = some (.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length))) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    rw [List.getElem?_set, List.getElem?_set]
    simp only [if_neg (by omega : ¬ (2 = 0)),
      if_pos (rfl : (0 : Nat) = 0)]
    simp [hg0len]
  have hpgB : stB.mem.pages = st1.mem.pages := by
    rw [hstB]
    dsimp only
    rw [write8_pages, hpg]
  have hg2S : stB.globals.globals[2]? = some (.i64 (g2 + 1)) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    rw [List.getElem?_set]
    simp [hg2len]
  have hg3S : ((stB.globals.globals.set 0 (Value.i64 (g0 + 48 + allocSizeU (UInt64.ofNat bytes.length) + 48 + 56))).set 2 (Value.i64 (g2 + 1 + 1)))[3]? = some (Value.i64 g3) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    simp [List.getElem?_set, hglen]
    exact (List.getElem?_eq_some_iff.mp hg3).choose_spec
  have hlenB : stB.globals.globals.length = st1.globals.globals.length := by
    rw [hstB]
    dsimp only
    rw [hgl]
    simp
  have h0B : 0 < stB.globals.globals.length := by omega
  have h2B : 2 < stB.globals.globals.length := by omega
  have h3B : 3 < stB.globals.globals.length := by omega
  have hh24e : stB.mem.read64 (UInt32.ofNat ((g0.toNat + 24) % 4294967296)) = 0 := by
    rw [hstB]
    dsimp only
    rw [read64_write8_ne _ _ _ _
      (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
    exact hh24
  have hg1B : stB.globals.globals[1]? = some (.i64 0) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    rw [List.getElem?_set, List.getElem?_set]
    simp only [if_neg (by omega : ¬ (2 = 1)), if_neg (by omega : ¬ (0 = 1))]
    exact hg1
  have hg4B : stB.globals.globals[4]? = some (.i64 g4) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    simp [List.getElem?_set, hglen]
    exact hg4
  have hg5B : stB.globals.globals[5]? = some (.i64 g5) := by
    rw [hstB]
    dsimp only
    rw [hgl]
    simp [List.getElem?_set, hglen]
    exact hg5
  exact ⟨hg0S, hpgB, hg2S, hg3S, hlenB, h0B, h2B, h3B, hh0e, hh24e, hg1B, hg4B, hg5B, hh8e⟩

end Project.PairFree.Spec
