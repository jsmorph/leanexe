import Project.ClobPostOnly.AppendTradeBump
import Interpreter.Wasm.Wp.Block
import Interpreter.Wasm.Wp.Loop

/-!
# Empty trade-array allocation

The successful `postOnly` branch allocates an empty trade array after it has
finished the appended order array.  This module isolates the generated
allocator suffix and its final result loads.  Its theorem can therefore compile
independently of the order-copy loop.
-/

namespace Project.ClobPostOnly.AppendTrade

open Wasm Project.Common Project.Clob Project.ClobPostOnly
  Project.ClobPostOnly.Allocation

set_option maxHeartbeats 8000000
set_option maxRecDepth 1048576

abbrev appendTradeAllocFrame := AppendTradeBump.appendTradeAllocFrame

def appendTradeScanBodyProg : Wasm.Program :=
  [
      .localGet 43,
      .constI64 (0 : UInt64),
      .eqI64,
      .br_if 1,
      .localGet 46,
      .constI64 (0 : UInt64),
      .neI64,
      .br_if 1,
      .localGet 43,
      .constI64 (32 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 44,
      .localGet 43,
      .constI64 (8 : UInt64),
      .subI64,
      .wrapI64,
      .load64 (0 : UInt32),
      .localSet 45,
      .localGet 44,
      .localGet 41,
      .geUI64,
      .iff 0 0 [
        .localGet 42,
        .constI64 (0 : UInt64),
        .eqI64,
        .iff 0 0 [
          .localGet 45,
          .globalSet 1
        ] [
          .localGet 42,
          .constI64 (8 : UInt64),
          .subI64,
          .wrapI64,
          .localGet 45,
          .store64 (0 : UInt32)
        ],
        .localGet 43,
        .constI64 (48 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (5501223100278326855 : UInt64),
        .store64 (0 : UInt32),
        .localGet 43,
        .constI64 (40 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (1 : UInt64),
        .store64 (0 : UInt32),
        .localGet 43,
        .constI64 (32 : UInt64),
        .subI64,
        .wrapI64,
        .localGet 44,
        .store64 (0 : UInt32),
        .localGet 43,
        .constI64 (24 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (2 : UInt64),
        .store64 (0 : UInt32),
        .localGet 43,
        .constI64 (16 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (4 : UInt64),
        .store64 (0 : UInt32),
        .localGet 43,
        .constI64 (8 : UInt64),
        .subI64,
        .wrapI64,
        .constI64 (0 : UInt64),
        .store64 (0 : UInt32),
        .localGet 43,
        .localSet 46
      ] [
        .localGet 43,
        .localSet 42,
        .localGet 45,
        .localSet 43
      ],
      .br 0
]

def appendTradeProg : Wasm.Program :=
  [
  .block 0 0 [
    .loop 0 0 appendTradeScanBodyProg
  ],
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

abbrev appendTradePost := AppendTradeBump.appendTradePost

abbrev appendTradeAssertion := AppendTradeBump.appendTradeAssertion

set_option Elab.async false in
theorem appendTradeScanBodyProg_spec (env : HostEnv Unit) (st : Store Unit)
    (ptr g0 : UInt64) (os : List OrderL) (order : OrderL)
    (Q : Assertion Unit)
    (hBreak : Q (.Break 1 st
      (appendTradeAllocFrame ptr g0 order os.length))) :
    wp «module» appendTradeScanBodyProg Q st
      (appendTradeAllocFrame ptr g0 order os.length) env := by
  simp only [appendTradeScanBodyProg, appendTradeAllocFrame,
    AppendTradeBump.appendTradeAllocFrame,
    AppendTradeBumpChecks.appendTradeAllocFrame]
  wp_run
  exact hBreak

set_option Elab.async false in
theorem appendTradeProg_spec (env : HostEnv Unit) (st0 st6 : Store Unit)
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
    (_hg1 : st6.globals.globals[1]? = some (.i64 0))
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
    wp «module» appendTradeProg
      (appendTradeAssertion st0 g0 g2 os order) st6
      (appendTradeAllocFrame ptr g0 order os.length) env := by
  simp only [appendTradeProg]
  apply wp_block_cons
  apply wp_loop_cons
    (Inv := fun st7 s7 => st7 = st6 ∧
      s7 = appendTradeAllocFrame ptr g0 order os.length)
    (μ := fun _ _ => 0)
  · exact ⟨rfl, rfl⟩
  · rintro st7 s7 ⟨hst, hs⟩
    subst st7
    subst s7
    refine appendTradeScanBodyProg_spec env st6 ptr g0 os order _ ?_
    have hBump := AppendTradeBump.appendTradeBumpProg_spec env st0 st6 ptr g0
      g2 os order hnewNat hbytesU htop hFit32 hFit hPages hg0 hg2 hBook
      hFresh hPageFrame hGlobalFrame hLowFrame
    simpa only [wp_nil, appendTradeAssertion, appendTradeAllocFrame,
      AppendTradeBump.appendTradeBumpProg,
      AppendTradeBump.appendTradeAllocFrame,
      AppendTradeBumpChecks.appendTradeAllocFrame, List.take, List.drop,
      List.nil_append] using hBump

end Project.ClobPostOnly.AppendTrade
