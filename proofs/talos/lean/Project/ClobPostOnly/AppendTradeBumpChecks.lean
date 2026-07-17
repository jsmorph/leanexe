import Project.ClobPostOnly.AppendTradeBranchStore

/-!
# Trade-array bump checks

This module proves the address and page-capacity checks before the trade-array
header writes.  The theorem accepts an opaque continuation for the header
program, so symbolic execution cannot expand the stores or the outer tail.  The
result separates control-flow arithmetic from memory initialization.
-/

namespace Project.ClobPostOnly.AppendTradeBumpChecks

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

def appendTradeAllocFrame (ptr g0 : UInt64) (order : OrderL)
    (n : Nat) : Locals :=
  { params := [.i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty],
    locals := [.i64 0, .i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 1, .i64 0, .i64 ptr, .i64 order.oid, .i64 order.otrader,
      .i64 order.oside, .i64 order.oprice, .i64 order.oqty,
      .i64 0, .i64 0, .i64 0, .i64 ptr, .i64 (g0 + 48),
      .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
      .i64 (g0 + 48), .i64 0, .i64 ptr, .i64 (UInt64.ofNat n),
      .i64 (UInt64.ofNat n * 5), .i64 (UInt64.ofNat n + 1),
      .i64 (g0 + 48), .i64 (UInt64.ofNat (n * 5)),
      .i64 order.oid, .i64 8, .i64 0, .i64 0, .i64 order.oqty,
      .i64 0, .i64 0, .i64 (orderArrayBytesU (n + 1)),
      .i64 0, .i64 0, .i64 (g0 + 48 + orderArrayBytesU (n + 1)),
      .i64 ((g0 + 48 + orderArrayBytesU (n + 1) - 1) / 65536 + 1),
      .i64 (g0 + 48)],
    values := [] }

def appendTradeBumpBranchProg : Wasm.Program :=
  [
  .globalGet 0,
  .constI64 (48 : UInt64),
  .addI64,
  .localGet 41,
  .addI64,
  .localSet 44,
  .localGet 44,
  .globalGet 0,
  .ltUI64,
  .iff 0 0 [
    .unreachable
  ] [],
  .localGet 44,
  .constI64 (1 : UInt64),
  .subI64,
  .constI64 (65536 : UInt64),
  .divUI64,
  .constI64 (1 : UInt64),
  .addI64,
  .localSet 45,
  .memorySize,
  .extendUI32,
  .localGet 45,
  .ltUI64,
  .iff 0 0 [
    .localGet 45,
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
  .localSet 46,
  .localGet 44,
  .globalSet 0,
  .localGet 46,
  .constI64 (48 : UInt64),
  .subI64,
  .wrapI64,
  .constI64 (5501223100278326855 : UInt64),
  .store64 (0 : UInt32),
  .localGet 46,
  .constI64 (40 : UInt64),
  .subI64,
  .wrapI64,
  .constI64 (1 : UInt64),
  .store64 (0 : UInt32),
  .localGet 46,
  .constI64 (32 : UInt64),
  .subI64,
  .wrapI64,
  .localGet 41,
  .store64 (0 : UInt32),
  .localGet 46,
  .constI64 (24 : UInt64),
  .subI64,
  .wrapI64,
  .constI64 (2 : UInt64),
  .store64 (0 : UInt32),
  .localGet 46,
  .constI64 (16 : UInt64),
  .subI64,
  .wrapI64,
  .constI64 (4 : UInt64),
  .store64 (0 : UInt32),
  .localGet 46,
  .constI64 (8 : UInt64),
  .subI64,
  .wrapI64,
  .constI64 (0 : UInt64),
  .store64 (0 : UInt32)
]

set_option Elab.async false in
theorem appendTradeBumpBranchProg_spec (env : HostEnv Unit)
    (st6 : Store Unit) (ptr g0 : UInt64) (os : List OrderL) (order : OrderL)
    (Q : Assertion Unit)
    (htop : (g0 + 48 + orderArrayBytesU (os.length + 1)).toNat =
      g0.toNat + 48 + orderArrayBytes (os.length + 1))
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st6.mem.pages * 65536)
    (hPages : st6.mem.pages ≤ 65536)
    (hg0 : st6.globals.globals[0]? = some
      (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1))))
    (hHeader : wp «module» AppendTradeBranchStore.appendTradeBranchHeaderProg
      Q st6 (AppendTradeBranchStore.appendTradeCheckedFrame ptr g0 order
        os.length) env) :
    wp «module» appendTradeBumpBranchProg Q st6
      (appendTradeAllocFrame ptr g0 order os.length) env := by
  simp only [appendTradeBumpBranchProg, appendTradeAllocFrame]
  wp_run
  simp only [hg0]
  have hnoWrap : ¬
      (g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 + 8 <
        g0 + 48 + orderArrayBytesU (os.length + 1) := by
    rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add, UInt64.toNat_add]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h48, h8, htop]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hnoWrap])]
  wp_run
  simp
  have htop2 :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 + 8).toNat =
        g0.toNat + 104 + orderArrayBytes (os.length + 1) := by
    rw [UInt64.toNat_add, UInt64.toNat_add, htop]
    have h48 : (48 : UInt64).toNat = 48 := rfl
    have h8 : (8 : UInt64).toNat = 8 := rfl
    rw [h48, h8]
    omega
  have htopSub :
      ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 + 8 - 1).toNat =
        g0.toNat + 103 + orderArrayBytes (os.length + 1) := by
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [toNat_sub_le _ _ (by rw [h1, htop2]; omega), htop2]
    rw [h1]
    omega
  have hpagesNeeded :
      (((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 + 8 - 1) /
            65536 + 1).toNat =
        (g0.toNat + 103 + orderArrayBytes (os.length + 1)) /
            65536 + 1 := by
    rw [UInt64.toNat_add, UInt64.toNat_div, htopSub]
    have h65536 : (65536 : UInt64).toNat = 65536 := rfl
    have h1 : (1 : UInt64).toNat = 1 := rfl
    rw [h65536, h1]
    omega
  have hmemorySize :
      ((UInt32.ofNat st6.mem.pages).toUInt64).toNat = st6.mem.pages := by
    have hlt : st6.mem.pages < UInt32.size := by
      have hs : UInt32.size = 4294967296 := rfl
      omega
    have hnat : (UInt32.ofNat st6.mem.pages).toNat = st6.mem.pages :=
      UInt32.toNat_ofNat_of_lt' hlt
    simp [hnat]
  have hnoGrow : ¬
      ((UInt32.ofNat st6.mem.pages).toUInt64 <
        ((g0 + 48 + orderArrayBytesU (os.length + 1)) + 48 + 8 - 1) /
            65536 + 1) := by
    rw [UInt64.lt_iff_toNat_lt, hmemorySize, hpagesNeeded]
    omega
  refine wp_iff_cons rfl ?_
  rw [if_neg (by simp [hnoGrow])]
  simp only [wp_nil, List.take, List.drop, List.nil_append]
  simpa only [AppendTradeBranchStore.appendTradeBranchHeaderProg,
    AppendTradeBranchStore.appendTradeCheckedFrame,
    AppendTradeStore.appendTradeStoreHeaderProg,
    AppendTradeStore.appendTradeStoreFrame] using hHeader

end Project.ClobPostOnly.AppendTradeBumpChecks
