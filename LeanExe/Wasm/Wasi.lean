import LeanExe.IR.Wasi
import LeanExe.Wasi.Primitives
import LeanExe.Wasm.Binary

namespace LeanExe.Wasm.Binary.CoreWasm.Wasi

open LeanExe.Wasi (Primitive Operand Result Iovec primitives)

private def store32 (address : Nat) (value : List Instr) : List Instr :=
  i32Const address ++ value ++ i32Store

private def loadField (address : List Instr) (width : Nat) : List Instr :=
  address ++ if width == 8 then i64Load else
    (if width == 1 then i32Load8U else i32Load) ++ i64ExtendI32U ++
      (if width == 2 then i64Const 65535 ++ i64And else [])

private def load32 (address : Nat) : List Instr :=
  loadField (i32Const address) 4

private def localAddress (slot offset : Nat) : List Instr :=
  localGet slot ++ i64Const offset ++ [Instr.addI64] ++ i32WrapI64

private def increment (slot : Nat) : List Instr :=
  localGet slot ++ i64Const 1 ++ [Instr.addI64] ++ localSet slot

private def forCount (index count : Nat) (body : List Instr) : List Instr :=
  i64Const 0 ++ localSet index ++
    [Instr.block [Instr.loop (localGet index ++ localGet count ++ i64GeU ++
      [Instr.brIf 1] ++ body ++ increment index ++ [Instr.br 0])]]

private def failure (width errorLocal : Nat) : List Instr :=
  i64Const 0 ++ localGet errorLocal ++
    (List.replicate (width - 2) (i64Const 0)).flatten ++ returnOp

private def checkError (errorLocal : Nat) (onError : List Instr) : List Instr :=
  i64ExtendI32U ++ localTee errorLocal ++ i64Eqz ++
    [Instr.iff false [] (some onError)]

private def success (values : List Instr) : List Instr :=
  i64Const 1 ++ i64Const 0 ++ values ++ returnOp

private def importType (p : Primitive) : List UInt8 :=
  funcType (p.operands.map fun | .local64 _ => i64 | _ => i32)
    (match p.result with | .exit => [] | _ => [i32])

private def sourceType (p : Primitive) : List UInt8 :=
  funcType (List.replicate p.paramCount i64) (List.replicate p.result.width i64)

private def operand (bufferLocal : Nat) : Operand → List Instr
  | .local32 slot => localGet slot ++ i32WrapI64
  | .local64 slot => localGet slot
  | .address value => i32Const value
  | .buffer => localGet bufferLocal ++ i32WrapI64

private def primitiveBody (index releaseIndex : Nat) (p : Primitive) : List UInt8 :=
  let errorLocal := p.paramCount
  let bufferLocal := errorLocal + 1
  let lengthLocal := errorLocal + 2
  let scratch := errorLocal + 3
  let fail := failure p.result.width errorLocal
  let freeBuffer := localGet bufferLocal ++ call releaseIndex
  let invoke := p.operands.flatMap (operand bufferLocal) ++ call index
  let iovec := match p.iovec with
    | .none => []
    | .input pointer => store32 0 (localGet pointer ++ i32WrapI64) ++
        store32 4 (localGet (pointer + 1) ++ i32WrapI64)
    | .output => store32 0 (localGet bufferLocal ++ i32WrapI64) ++
        store32 4 (localGet lengthLocal ++ i32WrapI64)
  let code := match p.result with
    | .errno => invoke ++ i64ExtendI32U
    | .exit => invoke ++ unreachable
    | .values fields =>
        iovec ++ invoke ++ checkError errorLocal fail ++
          success (fields.flatMap fun (offset, width) => loadField (i32Const (64 + offset)) width)
    | .buffer capacity counted flags =>
        localGet capacity ++ localSet lengthLocal ++
        rcAllocRawObject scratch (localGet lengthLocal) ++ localSet bufferLocal ++
        iovec ++ invoke ++ checkError errorLocal (freeBuffer ++ fail) ++
        (if counted then load32 64 ++ localSet lengthLocal else []) ++
        localGet capacity ++ localGet lengthLocal ++ i64LtU ++
          [Instr.iff false (i64Const 29 ++ localSet errorLocal ++ freeBuffer ++ fail) none] ++
        localGet lengthLocal ++ i64Eqz ++ [Instr.iff false
          (freeBuffer ++ i64Const 0 ++ localSet bufferLocal) none] ++
        success (localGet bufferLocal ++ localGet bufferLocal ++ localGet lengthLocal ++
          if flags then loadField (i32Const 68) 2 else [])
    | .preopenName | .strings _ | .events => unreachable
  bodyI (ofNats [1, 9, 126]) code

private def preopenNameBody (index prestatIndex releaseIndex : Nat) : List UInt8 :=
  let fail := localGet 3 ++ call releaseIndex ++ failure 5 1
  bodyI (ofNats [1, 9, 126]) <|
    localGet 0 ++ i32WrapI64 ++ i32Const 64 ++ call prestatIndex ++ checkError 1 fail ++
    load32 68 ++ localSet 2 ++
    rcAllocRawObject 4 (localGet 2) ++ localSet 3 ++
    localGet 0 ++ i32WrapI64 ++ localGet 3 ++ i32WrapI64 ++ localGet 2 ++ i32WrapI64 ++
      call index ++ checkError 1 fail ++
    success (localGet 3 ++ localGet 3 ++ localGet 2)

private def stringsBody (index sizesIndex releaseIndex : Nat) : List UInt8 :=
  -- Locals: errno, count, bytes, table, data, array, index, pointer, length, end, rc, allocator scratch.
  let cleanup := localGet 3 ++ call releaseIndex ++ localGet 4 ++ call releaseIndex ++
    localGet 5 ++ call releaseIndex
  let fail := cleanup ++ failure 4 0
  let invalid := i64Const 29 ++ localSet 0 ++ fail
  let cell (slot : Nat) := arraySlotAddress 3 slot (localGet 5) (localGet 6)
  bodyI (ofNats [1, 17, 126]) <|
    i32Const 64 ++ i32Const 68 ++ call sizesIndex ++ checkError 0 fail ++
    load32 64 ++ localSet 1 ++ load32 68 ++ localSet 2 ++
    rcAllocRawObject 11 (localGet 1 ++ i64Const 4 ++ [Instr.mulI64]) ++ localSet 3 ++
    rcAllocRawObject 11 (localGet 2) ++ localSet 4 ++
    localGet 3 ++ i32WrapI64 ++ localGet 4 ++ i32WrapI64 ++ call index ++ checkError 0 fail ++
    rcAllocArrayObject 11 3 1 (localGet 1) ++ localSet 5 ++
    localAddress 5 0 ++ i64Const 0 ++ i64Store ++
    localGet 4 ++ localGet 2 ++ [Instr.addI64] ++ localSet 9 ++
    forCount 6 1 (
      localGet 3 ++ localGet 6 ++ i64Const 4 ++ [Instr.mulI64, Instr.addI64] ++
        i32WrapI64 ++ i32Load ++ i64ExtendI32U ++ localSet 7 ++
      localGet 7 ++ localGet 4 ++ i64LtU ++ [Instr.iff false invalid none] ++
      i64Const 0 ++ localSet 8 ++
      [Instr.block [Instr.loop (
        localGet 7 ++ localGet 8 ++ [Instr.addI64] ++ localGet 9 ++ i64GeU ++
          [Instr.iff false invalid none] ++
        localGet 7 ++ localGet 8 ++ [Instr.addI64] ++ i32WrapI64 ++ i32Load8U ++
          [Instr.eqzI32, Instr.brIf 1] ++ increment 8 ++ [Instr.br 0])]] ++
      emitRetainLocal 4 10 ++
      cell 0 ++ localGet 4 ++ i64Store ++ cell 1 ++ localGet 7 ++ i64Store ++
      cell 2 ++ localGet 8 ++ i64Store ++
      localAddress 5 0 ++ localGet 6 ++ i64Const 1 ++ [Instr.addI64] ++ i64Store) ++
    localGet 3 ++ call releaseIndex ++ localGet 4 ++ call releaseIndex ++
    success (localGet 5 ++ localGet 5)

private def pollBody (index releaseIndex : Nat) : List UInt8 :=
  -- Locals: input array, errno, count, subscriptions, events, result, index, address, returned count, scratch.
  let cleanup := localGet 4 ++ call releaseIndex ++ localGet 5 ++ call releaseIndex
  let fail := cleanup ++ failure 4 2
  let invalid := i64Const 28 ++ localSet 2 ++ fail
  let source (slot : Nat) := arraySlotAddress 6 slot (localGet 1) (localGet 7) ++ i64Load
  let write (offset slot : Nat) (wide : Bool) := localAddress 8 offset ++ source slot ++
    (if wide then i64Store else i32WrapI64 ++ i32Store)
  let eventFields := [(0, 8), (8, 2), (10, 1), (16, 8), (24, 2)]
  bodyI (ofNats [1, 14, 126]) <|
    localAddress 1 0 ++ i64Load ++ localSet 3 ++
    localGet 3 ++ i64Eqz ++ [Instr.iff false invalid none] ++
    rcAllocRawObject 10 (localGet 3 ++ i64Const 48 ++ [Instr.mulI64]) ++ localSet 4 ++
    rcAllocRawObject 10 (localGet 3 ++ i64Const 32 ++ [Instr.mulI64]) ++ localSet 5 ++
    forCount 7 3 (
      localGet 4 ++ localGet 7 ++ i64Const 48 ++ [Instr.mulI64, Instr.addI64] ++ localSet 8 ++
      i64Const 2 ++ source 1 ++ i64LtU ++ [Instr.iff false invalid none] ++
      i64Const 65535 ++ source 5 ++ i64LtU ++ [Instr.iff false invalid none] ++
      (List.range 6).flatMap (fun i => localAddress 8 (i * 8) ++ i64Const 0 ++ i64Store) ++
      write 0 0 true ++ write 8 1 false ++ write 16 2 false ++ write 24 3 true ++
      write 32 4 true ++ write 40 5 false ++
      localGet 5 ++ localGet 7 ++ i64Const 32 ++ [Instr.mulI64, Instr.addI64] ++ localSet 8 ++
      (List.range 4).flatMap (fun i => localAddress 8 (i * 8) ++ i64Const 0 ++ i64Store)) ++
    localGet 4 ++ i32WrapI64 ++ localGet 5 ++ i32WrapI64 ++ localGet 3 ++ i32WrapI64 ++
      i32Const 64 ++ call index ++ checkError 2 fail ++
    load32 64 ++ localSet 9 ++
    localGet 3 ++ localGet 9 ++ i64LtU ++ [Instr.iff false
      (i64Const 29 ++ localSet 2 ++ fail) none] ++
    rcAllocArrayObject 10 5 0 (localGet 9) ++ localSet 6 ++
    localAddress 6 0 ++ localGet 9 ++ i64Store ++
    forCount 7 9 (
      localGet 5 ++ localGet 7 ++ i64Const 32 ++ [Instr.mulI64, Instr.addI64] ++ localSet 8 ++
      (enumerate eventFields).flatMap (fun (slot, offset, width) =>
        arraySlotAddress 5 slot (localGet 6) (localGet 7) ++
          loadField (localAddress 8 offset) width ++ i64Store)) ++
    cleanup ++ success (localGet 6 ++ localGet 6)

private def startBody (entryIndex exitIndex : Nat) : List UInt8 :=
  bodyI (ofNats [0]) (call entryIndex ++ i32WrapI64 ++ call exitIndex ++ unreachable)

def moduleBytes (program : LeanExe.IR.WasiProgram) : Except String ByteArray := do
  let module_ := program.module
  if program.entryIndex >= module_.funcs.size then throw "invalid WASI entry index"
  let count := primitives.size
  let shifted := shiftModuleCalls count module_
  let startIndex := count + shifted.funcs.size + count
  let releaseIndex := startIndex + 1
  let indexOf (name : String) : Except String Nat :=
    match primitives.findIdx? (fun p => p.name == name) with
    | some i => .ok i
    | none => .error s!"missing WASI import: {name}"
  let exitIndex ← indexOf "proc_exit"
  let wrappers ← (enumerate primitives.toList).mapM fun (i, p) => do
    match p.result with
    | .preopenName => .ok (preopenNameBody i (← indexOf "fd_prestat_get") releaseIndex)
    | .strings name => .ok (stringsBody i (← indexOf name) releaseIndex)
    | .events => .ok (pollBody i releaseIndex)
    | _ => .ok (primitiveBody i releaseIndex p)
  let sourceTypes := shifted.funcs.toList.map typeForFunc ++ primitives.toList.map sourceType ++
    [wasiStartType, funcType [i64] []]
  .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0] ++
    (wasmSection 1 <| vec (primitives.toList.map importType ++ sourceTypes)) ++
    (wasmSection 2 <| vec ((enumerate primitives.toList).map fun (i, p) =>
      importEntry "wasi_snapshot_preview1" p.name i)) ++
    (wasmSection 3 <| u32Vec ((List.range sourceTypes.length).map (· + count))) ++
    coreMemorySection ++ coreGlobalSection ++
    (wasmSection 7 <| vec [exportEntry "memory" 2 0, exportEntry "_start" 0 startIndex]) ++
    (wasmSection 10 <| vec (shifted.funcs.toList.map (emitFuncBody releaseIndex) ++ wrappers ++
      [startBody (program.entryIndex + count) exitIndex, coreReleaseBody releaseIndex]))).toArray

end LeanExe.Wasm.Binary.CoreWasm.Wasi
