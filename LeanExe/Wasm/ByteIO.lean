import LeanExe.IR.ByteIO
import LeanExe.Wasm.Binary

namespace LeanExe.Wasm.Binary.CoreWasm.ByteIO

private def importCount : Nat := 6

private def imports : List UInt8 :=
  wasmSection 2 <| vec [
    importEntry "wasi_snapshot_preview1" "fd_read" 0,
    importEntry "wasi_snapshot_preview1" "fd_write" 0,
    importEntry "wasi_snapshot_preview1" "fd_fdstat_set_flags" 1,
    importEntry "wasi_snapshot_preview1" "clock_time_get" 2,
    importEntry "wasi_snapshot_preview1" "poll_oneoff" 0,
    importEntry "wasi_snapshot_preview1" "proc_exit" 3]

private def importTypes : List (List UInt8) :=
  [wasiFdIoType, funcType [i32, i32] [i32],
    funcType [i32, i64, i32] [i32], wasiProcExitType]

private def store32 (address : Nat) (value : List Instr) : List Instr :=
  i32Const address ++ value ++ i32Store

private def store64 (address : Nat) (value : List Instr) : List Instr :=
  i32Const address ++ value ++ i64Store

private def checkError (errorLocal : Nat) (failure : List Instr) : List Instr :=
  i64ExtendI32U ++ localTee errorLocal ++ i64Eqz ++
    [Instr.iff false [] (some failure)]

private def clock : List Instr :=
  i32Const 1 ++ i64Const 0 ++ i32Const 16 ++ call 3

private def deadline (timeoutLocal deadlineLocal errorLocal : Nat)
    (failure : List Instr) : List Instr :=
  clock ++ checkError errorLocal failure ++
    i32Const 16 ++ i64Load ++ localGet timeoutLocal ++ [Instr.addI64] ++ localSet deadlineLocal ++
    localGet deadlineLocal ++ i32Const 16 ++ i64Load ++ i64LtU ++
    [Instr.iff false (i64Const 18446744073709551615 ++ localSet deadlineLocal) none]

private def waitBody : List UInt8 :=
  let failure := localGet 2 ++ returnOp
  let timeout := i64Const 73 ++ returnOp
  bodyI (ofNats [1, 1, 126]) <|
    clock ++ checkError 2 failure ++
    i32Const 16 ++ i64Load ++ localGet 1 ++ i64GeU ++
    [Instr.iff false timeout none] ++
    (List.range 12).flatMap (fun i => store64 (64 + i * 8) (i64Const 0)) ++
    store32 80 (i32Const 1) ++ store64 88 (localGet 1) ++ store32 104 (i32Const 1) ++
    store64 112 (i64Const 1) ++ store32 120 (localGet 0 ++ i32WrapI64) ++
    store32 128 (localGet 0 ++ i64Const 1 ++ [Instr.subI64] ++ i32WrapI64) ++
    i32Const 64 ++ i32Const 160 ++ i32Const 2 ++ i32Const 224 ++ call 4 ++
    checkError 2 failure ++
    clock ++ checkError 2 failure ++
    i32Const 16 ++ i64Load ++ localGet 1 ++ i64GeU ++
    [Instr.iff false timeout none] ++
    i32Const 160 ++ i64Load ++ i64Const 1 ++ i64Eq ++
    [Instr.iff false
      (i32Const 168 ++ i32Load ++ i64ExtendI32U ++ i64Const 65535 ++ i64And ++ returnOp)
      none] ++
    i32Const 224 ++ i32Load ++ i32Const 2 ++ i32Eq ++
    [Instr.iff false
      (i32Const 200 ++ i32Load ++ i64ExtendI32U ++ i64Const 65535 ++ i64And ++ returnOp)
      none] ++ timeout

private def readBody (waitIndex releaseIndex : Nat) : List UInt8 :=
  let failure := localGet 4 ++ call releaseIndex ++
    i64Const 0 ++ localGet 2 ++ i64Const 0 ++ i64Const 0 ++ i64Const 0 ++ returnOp
  let failWith (code : Nat) := i64Const code ++ localSet 2 ++ failure
  let success := i64Const 1 ++ i64Const 0 ++ localGet 4 ++ localGet 4 ++ localGet 5 ++ returnOp
  bodyI (ofNats [1, 10, 126]) <|
    localGet 0 ++ i64Eqz ++ [Instr.iff false (failWith 28) none] ++
    i64Const 4294967295 ++ localGet 0 ++ i64LtU ++ [Instr.iff false (failWith 28) none] ++
    deadline 1 3 2 failure ++
    i32Const 0 ++ i32Const 4 ++ call 2 ++ checkError 2 failure ++
    rcAllocRawObject 6 (localGet 0) ++ localSet 4 ++
    [Instr.loop (
      store32 0 (localGet 4 ++ i32WrapI64) ++ store32 4 (localGet 0 ++ i32WrapI64) ++
      i32Const 0 ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call 0 ++
      i64ExtendI32U ++ localSet 2 ++
      localGet 2 ++ i64Eqz ++ [Instr.iff false (
        i32Const 8 ++ i32Load ++ i64ExtendI32U ++ localSet 5 ++
        localGet 0 ++ localGet 5 ++ i64LtU ++ [Instr.iff false (failWith 29) none] ++
        localGet 5 ++ i64Eqz ++ [Instr.iff false
          (localGet 4 ++ call releaseIndex ++ i64Const 0 ++ localSet 4) none] ++ success) none] ++
      localGet 2 ++ i64Const 6 ++ i64Eq ++
        [Instr.iff false [] (some (localGet 2 ++ i64Const 27 ++ i64Ne ++
          [Instr.iff false failure none]))] ++
      i64Const 1 ++ localGet 3 ++ call waitIndex ++ localTee 2 ++ i64Eqz ++
        [Instr.iff false [] (some failure)] ++ [Instr.br 0])] ++ unreachable

private def writeBody (waitIndex : Nat) : List UInt8 :=
  let failure := localGet 4 ++ returnOp
  let success := i64Const 0 ++ returnOp
  let failWith (code : Nat) := i64Const code ++ localSet 4 ++ failure
  bodyI (ofNats [1, 5, 126]) <|
    localGet 2 ++ i64Eqz ++ [Instr.iff false success none] ++
    deadline 3 5 4 failure ++
    i32Const 1 ++ i32Const 4 ++ call 2 ++ checkError 4 failure ++
    localGet 1 ++ localSet 6 ++ localGet 2 ++ localSet 7 ++
    [Instr.loop (
      store32 0 (localGet 6 ++ i32WrapI64) ++ store32 4 (localGet 7 ++ i32WrapI64) ++
      i32Const 1 ++ i32Const 0 ++ i32Const 1 ++ i32Const 8 ++ call 1 ++
      i64ExtendI32U ++ localSet 4 ++
      localGet 4 ++ i64Eqz ++ [Instr.iff false (
        i32Const 8 ++ i32Load ++ i64ExtendI32U ++ localSet 8 ++
        localGet 8 ++ i64Eqz ++ [Instr.iff false (failWith 29) none] ++
        localGet 7 ++ localGet 8 ++ i64LtU ++ [Instr.iff false (failWith 29) none] ++
        localGet 6 ++ localGet 8 ++ [Instr.addI64] ++ localSet 6 ++
        localGet 7 ++ localGet 8 ++ [Instr.subI64] ++ localTee 7 ++ i64Eqz ++
          [Instr.iff false success none] ++
        clock ++ checkError 4 failure ++
        i32Const 16 ++ i64Load ++ localGet 5 ++ i64GeU ++
          [Instr.iff false (failWith 73) none] ++ [Instr.br 1]) none] ++
      localGet 4 ++ i64Const 6 ++ i64Eq ++
        [Instr.iff false [] (some (localGet 4 ++ i64Const 27 ++ i64Ne ++
          [Instr.iff false failure none]))] ++
      i64Const 2 ++ localGet 5 ++ call waitIndex ++ localTee 4 ++ i64Eqz ++
        [Instr.iff false [] (some failure)] ++ [Instr.br 0])] ++ unreachable

private def startBody (entryIndex : Nat) : List UInt8 :=
  bodyI (ofNats [0]) (call entryIndex ++ i32WrapI64 ++ call 5 ++ unreachable)

def moduleBytes (program : LeanExe.IR.ByteIOProgram) : Except String ByteArray := do
  let module_ := program.module
  if program.entryIndex >= module_.funcs.size then throw "invalid ByteIO entry index"
  let shifted := shiftModuleCalls importCount module_
  let startIndex := shifted.funcs.size + importCount + 2
  let releaseIndex := startIndex + 1
  let waitIndex := startIndex + 2
  let bodies := shifted.funcs.toList.map (emitFuncBody releaseIndex)
  .ok <| ByteArray.mk <| (ofNats [0, 97, 115, 109, 1, 0, 0, 0] ++
    (wasmSection 1 <| vec (importTypes ++ shifted.funcs.toList.map typeForFunc ++
      [funcType [i64, i64] (List.replicate 5 i64), funcType (List.replicate 4 i64) [i64],
       wasiStartType, funcType [i64] [], funcType [i64, i64] [i64]])) ++
    imports ++
    (wasmSection 3 <| u32Vec ((List.range (shifted.funcs.size + 5)).map (· + importTypes.length))) ++
    coreMemorySection ++ coreGlobalSection ++
    (wasmSection 7 <| vec [exportEntry "memory" 2 0, exportEntry "_start" 0 startIndex]) ++
    (wasmSection 10 <| vec (bodies ++
      [readBody waitIndex releaseIndex, writeBody waitIndex,
       startBody (program.entryIndex + importCount), coreReleaseBody releaseIndex, waitBody]))).toArray

end LeanExe.Wasm.Binary.CoreWasm.ByteIO
