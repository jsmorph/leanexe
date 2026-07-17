import Project.ClobLimit.InternalFullBookAllocPrepare

/-!
# Complete full-book allocation

The current Limit invariant has an empty free list.  This module composes the
aligned-capacity prefix with the generated full-book search and bump fallback.
The search initialization occurs once in the prefix.
-/

namespace Project.ClobLimit.InternalFullBookAlloc

open Wasm Project.Clob Project.ClobLimit

def fullBookAllocProg : Wasm.Program :=
  InternalFullBookAllocPrepare.fullBookAllocPrepareProg ++
    InternalFullBookBump.fullBookSearchProg ++
    InternalFullBookBump.fullBookBumpProg

set_option Elab.async false in
theorem fullBookAllocProg_spec
    (env : HostEnv Unit) (st : Store Unit) (base : Locals)
    (n : Nat) (g0 capacity next : UInt64)
    (hParams : base.params.length = 11)
    (hLocals : base.locals.length = 64)
    (hValues : base.values = [])
    (hLengthLocal : base.locals[50]? = some (.i64 (UInt64.ofNat n)))
    (hCapacityLocal : base.locals[58]? = some (.i64 capacity))
    (hNextLocal : base.locals[59]? = some (.i64 next))
    (hn : n < UInt64.size)
    (hbytes : fixedArrayBytes n 5 + 7 < UInt64.size)
    (hTop : (g0 + 48 + fixedArrayBytesU n 5).toNat =
      g0.toNat + 48 + (fixedArrayBytesU n 5).toNat)
    (hFit32 : g0.toNat + 48 + (fixedArrayBytesU n 5).toNat <
      4294967296)
    (hFit : g0.toNat + 48 + (fixedArrayBytesU n 5).toNat ≤
      st.mem.pages * 65536)
    (hPages : st.mem.pages ≤ 65536)
    (hg0 : st.globals.globals[0]? = some (.i64 g0))
    (hg1 : st.globals.globals[1]? = some (.i64 0))
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hDone : wp «module» rest Q
      (fixedArrayAllocBumpStore st g0 (fixedArrayBytesU n 5) 5)
      (InternalFullBookBump.allocFrame base (fixedArrayBytesU n 5) 0 0
        (g0 + 48 + fixedArrayBytesU n 5)
        ((g0 + 48 + fixedArrayBytesU n 5 - 1) / 65536 + 1)
        (g0 + 48)) env) :
    wp «module» (fullBookAllocProg ++ rest) Q st base env := by
  have hNeed8 : 8 ≤ (fixedArrayBytesU n 5).toNat := by
    rw [fixedArrayBytesU_toNat n 5 hn (by decide) (by omega)]
    unfold fixedArrayBytes
    omega
  unfold fullBookAllocProg
  rw [List.append_assoc, List.append_assoc]
  apply InternalFullBookAllocPrepare.fullBookAllocPrepareProg_spec env st
    base n 0 capacity next hParams hLocals hValues hLengthLocal
    hCapacityLocal hNextLocal hn hbytes hg1 Q
      (InternalFullBookBump.fullBookSearchProg ++
        InternalFullBookBump.fullBookBumpProg ++ rest)
  have hBump := InternalFullBookBump.fullBookBumpProg_spec env st base g0
    (fixedArrayBytesU n 5) 0 capacity next hParams hLocals hValues hNeed8
    hTop hFit32 hFit hPages hg0 Q rest hDone
  exact InternalFullBookBump.fullBookSearchProg_empty env st base
    (fixedArrayBytesU n 5) 0 capacity next hParams hLocals hValues Q
    (InternalFullBookBump.fullBookBumpProg ++ rest) hBump

end Project.ClobLimit.InternalFullBookAlloc
