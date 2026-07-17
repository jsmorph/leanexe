import Project.ClobLimit.InternalPartialTradeAllocPrepare

/-!
# Complete partial-trade allocation

The current Limit invariant has an empty free list.  This module composes the
stride-four setup with the generated search and bump fallback.
-/

namespace Project.ClobLimit.InternalPartialTradeAlloc

open Wasm Project.Clob Project.ClobLimit

def partialTradeAllocProg : Wasm.Program :=
  InternalPartialTradeAllocPrepare.partialTradeAllocPrepareProg ++
    InternalTradeBump.tradeSearchProg ++ InternalTradeBump.tradeBumpProg

set_option Elab.async false in
theorem partialTradeAllocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g0 capacity next : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[48]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[60]? = some (.i64 capacity))
    (hNextLocal : base.locals[61]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : fixedArrayBytes n 4 + 7 < UInt64.size)
    (hTop : (g0 + 48 + fixedArrayBytesU n 4).toNat =
      g0.toNat + 48 + (fixedArrayBytesU n 4).toNat)
    (hFit32 : g0.toNat + 48 + (fixedArrayBytesU n 4).toNat <
      4294967296)
    (hFit : g0.toNat + 48 + (fixedArrayBytesU n 4).toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q
      (fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 4) 4)
      (InternalTradeBump.allocFrame base (fixedArrayBytesU n 4) 0 0
        (g0 + 48 + fixedArrayBytesU n 4)
        ((g0 + 48 + fixedArrayBytesU n 4 - 1) / 65536 + 1)
        (g0 + 48)) env) :
    wp «module» (partialTradeAllocProg ++ rest) Q st base env := by
  have hNeed8 : 8 ≤ (fixedArrayBytesU n 4).toNat := by
    rw [fixedArrayBytesU_toNat n 4 hn (by decide) (by omega)]
    unfold fixedArrayBytes
    omega
  unfold partialTradeAllocProg
  rw [List.append_assoc, List.append_assoc]
  apply InternalPartialTradeAllocPrepare.partialTradeAllocPrepareProg_spec env
    st base n 0 capacity next hParams hLocals hValues hLengthLocal
    hCapacityLocal hNextLocal hn hbytes hg1 Q
      (InternalTradeBump.tradeSearchProg ++
        InternalTradeBump.tradeBumpProg ++ rest)
  have hBump := InternalTradeBump.tradeBumpProg_spec env st base g0
    (fixedArrayBytesU n 4) 0 capacity next hParams hLocals hValues hNeed8
    hTop hFit32 hFit hPages hg0 Q rest hDone
  exact InternalTradeBump.tradeSearchProg_empty env st base
    (fixedArrayBytesU n 4) 0 capacity next hParams hLocals hValues Q
    (InternalTradeBump.tradeBumpProg ++ rest) hBump

end Project.ClobLimit.InternalPartialTradeAlloc
