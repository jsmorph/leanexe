import CodeLib

namespace LeanExeGen.GeneratedR4337040846e16beb.FormalSpec

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size = 1 then
    #[UInt64.ofNat (Nat.gcd (input[0]!).toNat 42)]
  else
    input

def heapReserveBytes (input : Array UInt64) : Nat :=
  if input.size = 1 then 64 else 0

end LeanExeGen.GeneratedR4337040846e16beb.FormalSpec

namespace LeanExeGen.GeneratedR4337040846e16beb.FormalSpec

def UInt64ArrayAt (store : Wasm.Store Unit) (ptr : UInt64) (values : Array UInt64) : Prop :=
  ptr.toNat + 8 * (values.size + 1) ≤ 4294967296 ∧
  ptr.toNat + 8 * (values.size + 1) ≤ store.mem.pages * 65536 ∧
  store.mem.read64 ptr.toUInt32 = UInt64.ofNat values.size ∧
  ∀ (i : Nat), (h : i < values.size) →
    store.mem.read64
      (ptr + UInt64.ofNat (8 * (i + 1))).toUInt32 = values[i]

def RuntimeReady (initial : Wasm.Store Unit) (inputPtr : UInt64) (input : Array UInt64) : Prop :=
  UInt64ArrayAt initial inputPtr input ∧
  ∃ heapTop allocs retains releases frees : UInt64,
    initial.globals.globals = [.i64 heapTop, .i64 0, .i64 allocs, .i64 retains,
      .i64 releases, .i64 frees] ∧
    inputPtr.toNat + 8 * (input.size + 1) ≤ heapTop.toNat ∧
    heapTop.toNat + 48 + 8 * ((expected input).size + 1) ≤ 4294967296 ∧
    heapTop.toNat + 48 + 8 * ((expected input).size + 1) ≤
      initial.mem.pages * 65536 ∧
    heapTop.toNat + heapReserveBytes input ≤ 4294967296 ∧
    heapTop.toNat + heapReserveBytes input ≤ initial.mem.pages * 65536 ∧
    initial.mem.pages ≤ 65536

def ArtifactSpec (module_ : Wasm.Module) : Prop :=
  ∃ entry, module_.findExport "compute" = some entry ∧
    ∀ (env : Wasm.HostEnv Unit) (initial : Wasm.Store Unit)
      (inputPtr : UInt64) (input : Array UInt64),
      RuntimeReady initial inputPtr input →
      Wasm.TerminatesWith env module_ entry initial [.i64 inputPtr]
        (fun final results => ∃ outputPtr,
          results = [.i64 outputPtr] ∧
          UInt64ArrayAt final outputPtr (expected input))

end LeanExeGen.GeneratedR4337040846e16beb.FormalSpec
