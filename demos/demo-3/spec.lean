import CodeLib

namespace LeanExeGen.GeneratedRd1e76d3580ead0d9.FormalSpec

def expected (input : Array UInt64) : Array UInt64 :=
  if input.size != 15 then
    #[0, 0]
  else
    let query := input[0]!
    if query = input[1]! then
      #[input[2]!, 1]
    else if query < input[1]! then
      if query = input[3]! then
        #[input[4]!, 1]
      else if query < input[3]! then
        if query = input[7]! then #[input[8]!, 1] else #[0, 0]
      else
        if query = input[9]! then #[input[10]!, 1] else #[0, 0]
    else
      if query = input[5]! then
        #[input[6]!, 1]
      else if query < input[5]! then
        if query = input[11]! then #[input[12]!, 1] else #[0, 0]
      else
        if query = input[13]! then #[input[14]!, 1] else #[0, 0]

end LeanExeGen.GeneratedRd1e76d3580ead0d9.FormalSpec

namespace LeanExeGen.GeneratedRd1e76d3580ead0d9.FormalSpec

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

end LeanExeGen.GeneratedRd1e76d3580ead0d9.FormalSpec
