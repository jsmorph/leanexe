import CodeLib

namespace LeanExeGen.GeneratedReb06c2a75684e92c.FormalSpec

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size != 21 then
    #[0, 0]
  else
    let query := input[0]!
    if input[1]! = query then
      #[input[2]!, 1]
    else if input[3]! = query then
      #[input[4]!, 1]
    else if input[5]! = query then
      #[input[6]!, 1]
    else if input[7]! = query then
      #[input[8]!, 1]
    else if input[9]! = query then
      #[input[10]!, 1]
    else if input[11]! = query then
      #[input[12]!, 1]
    else if input[13]! = query then
      #[input[14]!, 1]
    else if input[15]! = query then
      #[input[16]!, 1]
    else if input[17]! = query then
      #[input[18]!, 1]
    else if input[19]! = query then
      #[input[20]!, 1]
    else
      #[0, 0]

end LeanExeGen.GeneratedReb06c2a75684e92c.FormalSpec

namespace LeanExeGen.GeneratedReb06c2a75684e92c.FormalSpec

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

end LeanExeGen.GeneratedReb06c2a75684e92c.FormalSpec
