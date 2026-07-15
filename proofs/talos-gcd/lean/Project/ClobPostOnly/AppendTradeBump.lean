import Project.ClobPostOnly.AppendTradeBumpChecks
import Interpreter.Wasm.Wp.Block

/-!
# Empty trade-array bump allocation

The successful `postOnly` branch reaches this program after its free-list scan
finds no reusable allocation.  The program performs the bump allocation,
initializes an empty trade array, and loads the three public results.  Compiling
this proof separately keeps the scan and order-copy proofs out of its
elaboration unit.
-/

namespace Project.ClobPostOnly.AppendTradeBump

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

abbrev appendTradeAllocFrame := AppendTradeBumpChecks.appendTradeAllocFrame

def appendTradeBumpProg : Wasm.Program :=
  [
  .localGet 46,
  .constI64 (0 : UInt64),
  .eqI64,
  .iff 0 0 [
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
  ] [],
  .globalGet 2,
  .constI64 (1 : UInt64),
  .addI64,
  .globalSet 2,
  .localGet 46,
  .localSet 34,
  .localGet 34,
  .wrapI64,
  .constI64 (0 : UInt64),
  .store64 (0 : UInt32),
  .localGet 34,
  .localSet 26,
  .localGet 26,
  .localSet 33,
  .localGet 31,
  .localGet 32,
  .localGet 33
]

abbrev appendTradePost := AppendTradeStore.appendTradePost

abbrev appendTradeAssertion := AppendTradeStore.appendTradeAssertion

set_option Elab.async false in
theorem appendTradeBumpProg_spec (env : HostEnv Unit) (st0 st6 : Store Unit)
    (ptr g0 g2 : UInt64) (os : List OrderL) (order : OrderL)
    (hnewNat : (g0 + 48).toNat = g0.toNat + 48)
    (hbytesU : (orderArrayBytesU (os.length + 1)).toNat =
      orderArrayBytes (os.length + 1))
    (htop : (g0 + 48 + orderArrayBytesU (os.length + 1)).toNat =
      g0.toNat + 48 + orderArrayBytes (os.length + 1))
    (hFit32 : g0.toNat + 104 + orderArrayBytes (os.length + 1) <
      4294967296)
    (hFit : g0.toNat + 104 + orderArrayBytes (os.length + 1) ≤
      st6.mem.pages * 65536)
    (hPages : st6.mem.pages ≤ 65536)
    (hg0 : st6.globals.globals[0]? = some
      (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1))))
    (hg2 : st6.globals.globals[2]? = some (.i64 (g2 + 1)))
    (hBook : OrdersAt st6 (g0 + 48) (os ++ [order]))
    (hFresh : FreshOrderArrayAt st6 (g0 + 48)
      (orderArrayBytesU (os.length + 1)))
    (hPageFrame : st6.mem.pages = st0.mem.pages)
    (hGlobalFrame : st6.globals.globals =
      ((st0.globals.globals.set 0
        (.i64 (g0 + 48 + orderArrayBytesU (os.length + 1)))).set 2
          (.i64 (g2 + 1))))
    (hLowFrame : ∀ a : Nat, a < g0.toNat →
      st6.mem.bytes a = st0.mem.bytes a) :
    wp «module» appendTradeBumpProg
      (appendTradeAssertion st0 g0 g2 os order) st6
      (appendTradeAllocFrame ptr g0 order os.length) env := by
  simp only [appendTradeBumpProg, appendTradeAllocFrame,
    AppendTradeBumpChecks.appendTradeAllocFrame]
  wp_run
  refine wp_iff_cons rfl ?_
  rw [if_pos (by simp)]
  change wp «module» AppendTradeBumpChecks.appendTradeBumpBranchProg _ st6
    (AppendTradeBumpChecks.appendTradeAllocFrame ptr g0 order os.length) env
  have hHeader := AppendTradeBranchStore.appendTradeBranchHeaderProg_spec env
    st0 st6 ptr g0 g2 os order hnewNat hbytesU htop hFit32 hFit hg0 hg2
    hBook hFresh hPageFrame hGlobalFrame hLowFrame
  have hBranch := AppendTradeBumpChecks.appendTradeBumpBranchProg_spec env st6
    ptr g0 os order
    (AppendTradeBranchStore.appendTradeBranchContinuation env st0 g0 g2 os
      order) htop hFit32 hFit hPages hg0 hHeader
  refine wp.imp hBranch ?_
  intro c hc
  unfold AppendTradeBranchStore.appendTradeBranchContinuation at hc
  cases c with
  | Fallthrough st' s' =>
      simpa only [appendTradeAssertion,
        AppendTradeStore.appendTradeStoreTailProg, List.take, List.drop,
        List.nil_append] using hc
  | Break k st' s' =>
      cases k with
      | zero =>
          simpa only [appendTradeAssertion,
            AppendTradeStore.appendTradeStoreTailProg, List.take, List.drop,
            List.nil_append] using hc
      | succ k => simpa only [appendTradeAssertion] using hc
  | Return st' vs => simpa only [appendTradeAssertion] using hc
  | Trap st' msg => simpa only [appendTradeAssertion] using hc
  | Invalid msg => simpa only [appendTradeAssertion] using hc
  | OutOfFuel => simpa only [appendTradeAssertion] using hc
  | ReturnCall fid st' vs => simpa only [appendTradeAssertion] using hc
  | Throwing tag args st' s' => simpa only [appendTradeAssertion] using hc

end Project.ClobPostOnly.AppendTradeBump
