import Project.ClobPostOnly.Allocation
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Appended order-array copy

The successful `postOnly` branch copies the existing order words into a fresh
array before storing the appended order.  This module proves the generated copy
loop against a word-prefix invariant.  Its opaque continuation keeps later
stores and allocations outside this elaboration unit.
-/

namespace Project.ClobPostOnly.AppendOrderCopy

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

macro "wp_run_big" : tactic => `(tactic|
  simp (config := { maxSteps := 10000000 }) only [wp_simp,
    Locals.get, Locals.set?, Locals.validIndex,
    Function.toLocals, Function.numParams, Function.numLocals,
    List.take, List.drop, List.replicate, List.length, List.map,
    ValueType.zero, List.headD])

def appendCopyFrame (ptr g0 : UInt64) (order : OrderL)
    (n k : Nat) : Locals :=
  { params := [.i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty],
    locals := [.i64 0, .i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 1, .i64 0, .i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 0, .i64 0, .i64 0, .i64 ptr, .i64 0, .i64 0,
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 ptr, .i64 (UInt64.ofNat n),
      .i64 (UInt64.ofNat n * 5), .i64 (UInt64.ofNat n + 1),
      .i64 (g0 + 48), .i64 (UInt64.ofNat k),
      .i64 order.oid, .i64 order.otrader, .i64 order.oside,
      .i64 order.oprice, .i64 order.oqty, .i64 0, .i64 0,
      .i64 (orderArrayBytesU (n + 1)), .i64 0, .i64 0,
      .i64 (g0 + 48 + orderArrayBytesU (n + 1)),
      .i64 ((g0 + 48 + orderArrayBytesU (n + 1) - 1) / 65536 + 1),
      .i64 (g0 + 48)],
    values := [] }

def appendCopyInv (st0 : Store Unit) (ptr g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL) (total : Nat) : AssertionF Unit :=
  fun st s =>
    ∃ k : Nat, k ≤ total ∧
      s = appendCopyFrame ptr g0 order os.length k ∧
      st.mem.pages = st0.mem.pages ∧
      st.globals.globals =
        ((st0.globals.globals.set 0
          (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1)))).set 2
          (.i64 (g2 + 1))) ∧
      FreshOrderArrayAt st (g0 + 48)
        (orderArrayBytesU (os.length + 1)) ∧
      st.mem.read64 (g0 + 48).toUInt32 = UInt64.ofNat (os.length + 1) ∧
      (∀ a : Nat, a < g0.toNat → st.mem.bytes a = st0.mem.bytes a) ∧
      ∀ w : Nat, w < k → orderWord st (g0 + 48) w = orderWord st0 ptr w

def appendCopyMeasure (total : Nat) (_ : Store Unit) (s : Locals) : Nat :=
  match s.locals[33]? with
  | some (Value.i64 k) => total - k.toNat
  | _ => 0

def appendOrderCopyBodyProg : Wasm.Program :=
  [
  .localGet 39,
  .localGet 36,
  .geUI64,
  .br_if 1,
  .localGet 38,
  .localGet 39,
  .constI64 (1 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .localGet 34,
  .localGet 39,
  .constI64 (1 : UInt64),
  .addI64,
  .constI64 (8 : UInt64),
  .mulI64,
  .addI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .store64 (0 : UInt32),
  .localGet 39,
  .constI64 (1 : UInt64),
  .addI64,
  .localSet 39,
  .br 0
]

def appendOrderCopyProg : Wasm.Program :=
  [
  .block 0 0 [
    .loop 0 0 appendOrderCopyBodyProg
  ]
]

set_option Elab.async false in
theorem appendOrderCopyProg_spec (env : HostEnv Unit)
    (st0 st4 : Store Unit) (ptr g0 g2 : UInt64)
    (os : List OrderL) (order : OrderL)
    (hInput32 : ptr.toNat + (os.length * 5 + 1) * 8 < 4294967296)
    (hBelow : ptr.toNat + (os.length * 5 + 1) * 8 ≤ g0.toNat)
    (htotalU : (UInt64.ofNat os.length * 5).toNat = os.length * 5)
    (hnewNat : (g0 + 48).toNat = g0.toNat + 48)
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st0.mem.pages * 65536)
    (Q : Assertion Unit)
    (hInit : appendCopyInv st0 ptr g0 g2 os order (os.length * 5) st4
      (appendCopyFrame ptr g0 order os.length 0))
    (hDone : ∀ st5,
      appendCopyInv st0 ptr g0 g2 os order (os.length * 5) st5
        (appendCopyFrame ptr g0 order os.length (os.length * 5)) →
      Q (.Fallthrough st5
        (appendCopyFrame ptr g0 order os.length (os.length * 5)))) :
    wp «module» appendOrderCopyProg Q st4
      (appendCopyFrame ptr g0 order os.length 0) env := by
  simp only [appendOrderCopyProg]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := appendCopyInv st0 ptr g0 g2 os order (os.length * 5))
    (μ := appendCopyMeasure (os.length * 5))
  · exact hInit
  · rintro st5 s5
      ⟨k, hk, rfl, hpg, hgl, hfresh, hlength, hlo, hcopied⟩
    have hkU : (UInt64.ofNat k).toNat = k :=
      toNat_ofNat_lt (by rw [size_eq]; omega)
    simp only [appendOrderCopyBodyProg, appendCopyFrame]
    wp_run_big
    try simp
    by_cases hkend : k = os.length * 5
    · have hge : UInt64.ofNat k ≥ UInt64.ofNat os.length * 5 := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, htotalU]
        omega
      rw [if_pos hge]
      try simp
      subst k
      apply hDone
      exact ⟨os.length * 5, le_rfl, rfl, hpg, hgl, hfresh, hlength,
        hlo, hcopied⟩
    · have hnge : ¬ (UInt64.ofNat k ≥ UInt64.ofNat os.length * 5) := by
        rw [ge_iff_le, UInt64.le_iff_toNat_le, hkU, htotalU]
        omega
      rw [if_neg hnge]
      try simp
      have hklt : k < os.length * 5 := Nat.lt_of_le_of_ne hk hkend
      have hsrcRead :
          st5.mem.read64
              (UInt32.ofNat ((ptr.toNat + (k + 1) * 8) % 4294967296)) =
            orderWord st0 ptr k := by
        unfold orderWord
        apply read64_congr
        intro b hb
        rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt (by omega)]
        exact hlo _ (by omega)
      have hdstLt : g0.toNat + 48 + (k + 1) * 8 < 4294967296 := by
        unfold orderArrayBytes fixedArrayBytes at hFit32
        omega
      have hsrcBound :
          (ptr.toNat + (k + 1) * 8) % 4294967296 + 8 ≤
            st5.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt (by omega), hpg]
        have hFit' := hFit
        unfold orderArrayBytes fixedArrayBytes at hFit'
        omega
      have hdstBound :
          (g0.toNat + 48 + (k + 1) * 8) % 4294967296 + 8 ≤
            st5.mem.pages * 65536 := by
        rw [Nat.mod_eq_of_lt hdstLt, hpg]
        have hFit' := hFit
        unfold orderArrayBytes fixedArrayBytes at hFit'
        have hwordFit :
            g0.toNat + 48 + (k + 1) * 8 + 8 ≤
              g0.toNat + 48 + orderArrayBytes (os.length + 1) := by
          unfold orderArrayBytes fixedArrayBytes
          omega
        exact hwordFit.trans (by omega)
      rw [if_neg (Nat.not_lt.mpr hsrcBound),
        if_neg (Nat.not_lt.mpr hdstBound)]
      refine ⟨?_, ?_⟩
      · have hkNext : UInt64.ofNat k + 1 = UInt64.ofNat (k + 1) := by
          apply UInt64.toNat.inj
          rw [toNat_add_one (by rw [hkU, size_eq]; omega), hkU,
            toNat_ofNat_lt (by rw [size_eq]; omega)]
        refine ⟨k + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp only [appendCopyFrame, hkNext]
        · rw [Mem.write64_pages, hpg]
        · exact hgl
        · refine FreshFixedArrayAt.write64_data hfresh
            (by rw [hnewNat]; omega) ?_
          rw [hnewNat, toUInt32_ofNat_mod_toNat,
            Nat.mod_eq_of_lt hdstLt]
          omega
        · rw [read64_write64_ne _ _ _ _
            (by
              simp only [toUInt32_eq_ofNat, hnewNat,
                toUInt32_ofNat_mod_toNat]
              omega)]
          exact hlength
        · intro a ha
          rw [write64_bytes_lo _ _ _
            (by
              rw [toUInt32_ofNat_mod_toNat, Nat.mod_eq_of_lt hdstLt]
              omega)]
          exact hlo a ha
        · intro w hw
          unfold orderWord
          rw [hnewNat]
          by_cases hwk : w = k
          · subst w
            rw [Mem.read64_write64_same]
            have hs := hsrcRead
            unfold orderWord at hs
            exact hs
          · rw [read64_write64_ne _ _ _ _
                (by simp only [toUInt32_ofNat_mod_toNat]; omega)]
            have hc := hcopied w (by omega)
            unfold orderWord at hc
            rw [hnewNat] at hc
            exact hc
      · simp [appendCopyMeasure, hkU]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega

end Project.ClobPostOnly.AppendOrderCopy
