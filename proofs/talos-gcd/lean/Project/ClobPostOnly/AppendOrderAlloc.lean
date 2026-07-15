import Project.ClobPostOnly.AppendOrderCopy
import Project.FixedArrayAllocation
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Appended order-array allocation

The successful `postOnly` branch allocates the replacement order array before
copying its existing words.  This module proves the generated free-list scan,
bump allocation, header writes, and length initialization.  Its postcondition
is the copy-loop invariant at an empty prefix.
-/

namespace Project.ClobPostOnly.AppendOrderAlloc

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation Project.ClobPostOnly.AppendOrderCopy

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def appendAllocFrame (ptr : UInt64) (order : OrderL) (n : Nat) : Locals :=
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
      .i64 0, .i64 0, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 0, .i64 0,
      .i64 (orderArrayBytesU (n + 1)),
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
    values := [] }

def appendOrderAllocScanBodyProg : Wasm.Program :=
  [
  .localGet 49,
  .constI64 (0 : UInt64),
  .eqI64,
  .br_if 1,
  .localGet 52,
  .constI64 (0 : UInt64),
  .neI64,
  .br_if 1,
  .localGet 49,
  .constI64 (32 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 50,
  .localGet 49,
  .constI64 (8 : UInt64),
  .subI64,
  .wrapI64,
  .load64 (0 : UInt32),
  .localSet 51,
  .localGet 50,
  .localGet 47,
  .geUI64,
  .iff 0 0 [
    .localGet 48,
    .constI64 (0 : UInt64),
    .eqI64,
    .iff 0 0 [
      .localGet 51,
      .globalSet 1
    ] [
      .localGet 48,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .localGet 51,
      .store64 (0 : UInt32)
    ],
    .localGet 49,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 49,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 49,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 50,
    .store64 (0 : UInt32),
    .localGet 49,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 49,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5 : UInt64),
    .store64 (0 : UInt32),
    .localGet 49,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32),
    .localGet 49,
    .localSet 52
  ] [
    .localGet 49,
    .localSet 48,
    .localGet 51,
    .localSet 49
  ],
  .br 0
]

def appendOrderAllocProg : Wasm.Program :=
  [
  .block 0 0 [
    .loop 0 0 appendOrderAllocScanBodyProg
  ],
  .localGet 52,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localGet 47,
    .addI64,
    .localSet 50,
    .localGet 50,
    .globalGet 0,
    .ltUI64,
    .iff 0 0 [
      .unreachable
    ] [],
    .localGet 50,
    .constI64 (1 : UInt64),
    .subI64,
    .constI64 (65536 : UInt64),
    .divUI64,
    .constI64 (1 : UInt64),
    .addI64,
    .localSet 51,
    .memorySize,
    .extendUI32,
    .localGet 51,
    .ltUI64,
    .iff 0 0 [
      .localGet 51,
      .memorySize,
      .extendUI32,
      .subI64,
      .wrapI64,
      .memoryGrow,
      .const (4294967295 : UInt32),
      .eq,
      .iff 0 0 [
        .unreachable
      ] []
    ] [],
    .globalGet 0,
    .constI64 (48 : UInt64),
    .addI64,
    .localSet 52,
    .localGet 50,
    .globalSet 0,
    .localGet 52,
    .constI64 (48 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5501223100278326855 : UInt64),
    .store64 (0 : UInt32),
    .localGet 52,
    .constI64 (40 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (1 : UInt64),
    .store64 (0 : UInt32),
    .localGet 52,
    .constI64 (32 : UInt64),
    .subI64,
    .wrapI64,
    .localGet 47,
    .store64 (0 : UInt32),
    .localGet 52,
    .constI64 (24 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (2 : UInt64),
    .store64 (0 : UInt32),
    .localGet 52,
    .constI64 (16 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (5 : UInt64),
    .store64 (0 : UInt32),
    .localGet 52,
    .constI64 (8 : UInt64),
    .subI64,
    .wrapI64,
    .constI64 (0 : UInt64),
    .store64 (0 : UInt32)
  ] [],
  .globalGet 2,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 2,
  .localGet 52,
  .localSet 38,
  .localGet 38,
  .wrapI64,
  .localGet 37,
  .store64 (0 : UInt32),
  .constI64 (0 : UInt64),
  .localSet 39
]

set_option Elab.async false in
theorem appendOrderAllocProg_spec (env : HostEnv Unit) (st0 : Store Unit)
    (ptr g0 g2 : UInt64) (os : List OrderL) (order : OrderL)
    (hlenAdd : UInt64.ofNat os.length + 1 = UInt64.ofNat (os.length + 1))
    (hbytesU : (orderArrayBytesU (os.length + 1)).toNat =
      orderArrayBytes (os.length + 1))
    (htop : (g0 + 48 + orderArrayBytesU (os.length + 1)).toNat =
      g0.toNat + 48 + orderArrayBytes (os.length + 1))
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st0.mem.pages * 65536)
    (hPages : st0.mem.pages ≤ 65536)
    (hg0 : st0.globals.globals[0]? = some (.i64 g0))
    (hg2 : st0.globals.globals[2]? = some (.i64 g2))
    (Q : Assertion Unit)
    (hNext : ∀ st4,
      appendCopyInv st0 ptr g0 g2 os order (os.length * 5) st4
        (appendCopyFrame ptr g0 order os.length 0) →
      Q (.Fallthrough st4 (appendCopyFrame ptr g0 order os.length 0))) :
    wp «module» appendOrderAllocProg Q st0
      (appendAllocFrame ptr order os.length) env := by
  simp only [appendOrderAllocProg]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st s => st = st0 ∧ s = appendAllocFrame ptr order os.length)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st1 s1 ⟨hst, hs⟩
    subst st1
    subst s1
    simp only [appendOrderAllocScanBodyProg, appendAllocFrame]
    wp_run
    refine wp_iff_cons rfl ?_
    rw [if_pos (by simp)]
    wp_run
    simp only [hg0]
    have hnoWrap : ¬ g0 + 48 + orderArrayBytesU (os.length + 1) < g0 := by
      rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add,
        hbytesU]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48]
      omega
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnoWrap])]
    wp_run
    simp
    have htopSub :
        (g0 + 48 + orderArrayBytesU (os.length + 1) - 1).toNat =
          g0.toNat + 48 + orderArrayBytes (os.length + 1) - 1 := by
      rw [toNat_sub_le _ _ (by rw [htop]; simp; omega), htop]
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h1]
    have hpagesNeeded :
        ((g0 + 48 + orderArrayBytesU (os.length + 1) - 1) /
              65536 + 1).toNat =
          (g0.toNat + 48 + orderArrayBytes (os.length + 1) - 1) /
              65536 + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_div, htopSub]
      have h65536 : (65536 : UInt64).toNat = 65536 := rfl
      have h1 : (1 : UInt64).toNat = 1 := rfl
      rw [h65536, h1]
      omega
    have hmemorySize :
        ((UInt32.ofNat st0.mem.pages).toUInt64).toNat = st0.mem.pages := by
      have hlt : st0.mem.pages < UInt32.size := by
        have hs : UInt32.size = 4294967296 := rfl
        omega
      have hnat : (UInt32.ofNat st0.mem.pages).toNat = st0.mem.pages :=
        UInt32.toNat_ofNat_of_lt' hlt
      simp [hnat]
    have hnoGrow : ¬
        ((UInt32.ofNat st0.mem.pages).toUInt64 <
          (g0 + 48 + orderArrayBytesU (os.length + 1) - 1) / 65536 + 1) := by
      rw [UInt64.lt_iff_toNat_lt, hmemorySize, hpagesNeeded]
      omega
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnoGrow])]
    wp_run
    simp only [hg0]
    try wp_run
    try simp
    have hsub48 : (g0 + 48 - 48).toNat = g0.toNat := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsub40 : (g0 + 48 - 40).toNat = g0.toNat + 8 := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (40 : UInt64).toNat = 40 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsub32 : (g0 + 48 - 32).toNat = g0.toNat + 16 := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (32 : UInt64).toNat = 32 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsub24 : (g0 + 48 - 24).toNat = g0.toNat + 24 := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (24 : UInt64).toNat = 24 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsub16 : (g0 + 48 - 16).toNat = g0.toNat + 32 := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (16 : UInt64).toNat = 16 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hsub8 : (g0 + 48 - 8).toNat = g0.toNat + 40 := by
      rw [UInt64.toNat_sub, UInt64.toNat_add]
      have ha : (48 : UInt64).toNat = 48 := rfl
      have hb : (8 : UInt64).toNat = 8 := rfl
      rw [ha, hb]
      have hs : (18446744073709551616 : Nat) = UInt64.size := rfl
      omega
    have hnewNat : (g0 + 48).toNat = g0.toNat + 48 := by
      rw [UInt64.toNat_add]
      have h48 : (48 : UInt64).toNat = 48 := rfl
      rw [h48]
      omega
    have hFit' := hFit
    unfold orderArrayBytes fixedArrayBytes at hFit'
    have hBaseBound : g0.toNat % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase8Bound : (g0 + 48 - 40).toNat % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [hsub40, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase16Bound : (g0 + 48 - 32).toNat % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [hsub32, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase24Bound : (g0 + 48 - 24).toNat % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [hsub24, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase32Bound : (g0 + 48 - 16).toNat % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [hsub16, Nat.mod_eq_of_lt (by omega)]
      omega
    have hBase40Bound : (g0 + 48 - 8).toNat % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [hsub8, Nat.mod_eq_of_lt (by omega)]
      omega
    have hDataBound : (g0.toNat + 48) % 4294967296 + 8 ≤
        st0.mem.pages * 65536 := by
      rw [Nat.mod_eq_of_lt (by omega)]
      omega
    rw [if_neg (Nat.not_lt.mpr hBaseBound),
      if_neg (Nat.not_lt.mpr hBase8Bound),
      if_neg (Nat.not_lt.mpr hBase16Bound),
      if_neg (Nat.not_lt.mpr hBase24Bound),
      if_neg (Nat.not_lt.mpr hBase32Bound),
      if_neg (Nat.not_lt.mpr hBase40Bound)]
    simp only [hg2]
    rw [if_neg (Nat.not_lt.mpr hDataBound)]
    apply hNext
    refine ⟨0, Nat.zero_le _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [appendCopyFrame]
    · rfl
    · rfl
    · unfold FreshOrderArrayAt FreshFixedArrayAt
      simp only [toUInt32_eq_ofNat, hsub48, hsub40, hsub32, hsub24,
        hsub16, hsub8]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · read_frames
      · read_frames
      · read_frames
      · read_frames
      · read_frames
      · read_frames
    · rw [toUInt32_eq_ofNat, hnewNat, Mem.read64_write64_same, hlenAdd]
    · intro a ha
      have hLow := fixedArrayMem_bytes_before st0.mem g0
        (orderArrayBytesU (os.length + 1)) 5
        (UInt64.ofNat os.length + 1) a (by omega) ha
      simpa only [fixedArrayMem, hsub40, hsub32, hsub24, hsub16, hsub8,
        hnewNat] using hLow
    · intro w hw
      omega

end Project.ClobPostOnly.AppendOrderAlloc
