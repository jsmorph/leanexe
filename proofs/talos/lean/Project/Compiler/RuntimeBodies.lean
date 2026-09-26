import Project.Compiler.RuntimeParsing

namespace Project.Compiler.RuntimeEncoding

open LeanExe.Wasm.Binary.CoreWasm
open Project.Compiler.ArithmeticEncoding

/-- Construct checked raw syntax for the compiler's fixed runtime. This tactic
only applies the encoding relation's constructors; it does not trust evaluation
of the encoder or decoder. -/
macro "runtime_encoding" : tactic => `(tactic|
  repeat' first
    | apply RuntimeProgram.cons
    | exact RuntimeProgram.nil
    | apply RuntimeInstruction.control .block
    | apply RuntimeInstruction.control .loop
    | apply RuntimeInstruction.control .ifNone
    | apply RuntimeInstruction.ifElse
    | (apply RuntimeInstruction.atom
       first
         | exact RuntimeAtom.arithmetic (Atom.get _ (by decide))
         | exact RuntimeAtom.arithmetic (Atom.set _ (by decide))
         | exact RuntimeAtom.arithmetic (Atom.const _)
         | exact RuntimeAtom.arithmetic Atom.add
         | exact RuntimeAtom.arithmetic Atom.sub
         | exact RuntimeAtom.arithmetic Atom.mul
         | exact RuntimeAtom.arithmetic Atom.div
         | exact RuntimeAtom.arithmetic Atom.rem
         | exact RuntimeAtom.arithmetic Atom.and
         | exact RuntimeAtom.arithmetic Atom.or
         | exact RuntimeAtom.arithmetic Atom.xor
         | exact RuntimeAtom.arithmetic Atom.shl
         | exact RuntimeAtom.arithmetic Atom.shr
         | exact RuntimeAtom.arithmetic Atom.eq
         | exact RuntimeAtom.indexed .tee _ (by decide)
         | exact RuntimeAtom.indexed .globalGet _ (by decide)
         | exact RuntimeAtom.indexed .globalSet _ (by decide)
         | exact RuntimeAtom.indexed .call _ (by decide)
         | exact RuntimeAtom.indexed .br _ (by decide)
         | exact RuntimeAtom.indexed .brIf _ (by decide)
         | exact RuntimeAtom.plain .ne
         | exact RuntimeAtom.plain .lt
         | exact RuntimeAtom.plain .ge
         | exact RuntimeAtom.plain .wrap
         | exact RuntimeAtom.plain .extend
         | exact RuntimeAtom.plain .eq32
         | exact RuntimeAtom.plain .unreachable
         | exact RuntimeAtom.plain .ret
         | exact RuntimeAtom.plain .load64
         | exact RuntimeAtom.plain .store64
         | exact RuntimeAtom.plain .memorySize
         | exact RuntimeAtom.plain .memoryGrow
         | exact RuntimeAtom.plain .negOne))

/-- Raw syntax and a proof for the actual allocator instruction list. -/
def allocEncoding : { raw // RuntimeProgram coreAllocInstrs raw } := ⟨_, by
  dsimp [coreAllocInstrs, rcAllocRawObject, rcAllocPayload, rcInitHeader,
    rcHeaderStore, rcHeaderLoad, rcHeaderAddress, i64Align8, incGlobal,
    runtimeStatGlobal, localGet, localSet, localTee, globalGet, globalSet,
    i64Const, i64Eq, i64Ne, i64GeU, i64LtU, i32WrapI64, i64Load, i64Store,
    memorySize, memoryGrow, i64ExtendI32U, i32ConstNegOne, i32Eq, unreachable,
    List.append]
  runtime_encoding⟩

/-- Raw syntax and a proof for the actual statistics/reset instruction list. -/
def resetEncoding : { raw // RuntimeProgram coreResetInstrs raw } := ⟨_, by
  dsimp [coreResetInstrs, i64Const, globalSet, runtimeStatGlobal, List.append]
  runtime_encoding⟩

/-- Raw syntax and a proof for the actual retain instruction list. -/
def retainEncoding : { raw // RuntimeProgram coreRetainInstrs raw } := ⟨_, by
  dsimp [coreRetainInstrs, rcHeaderStore, rcHeaderLoad, rcHeaderAddress,
    incGlobal, runtimeStatGlobal, localGet, localSet, globalGet, globalSet,
    i64Const, i64Eq, i64Ne, i32WrapI64, i64Load, i64Store, unreachable,
    List.append]
  runtime_encoding⟩

/-- In a one-source-function module the existing runtime release index is four. -/
def releaseEncoding : { raw // RuntimeProgram (coreReleaseInstrs 4) raw } := ⟨_, by
  dsimp [coreReleaseInstrs, rcHeaderStore, rcHeaderLoad, rcHeaderAddress,
    incGlobal, runtimeStatGlobal, localGet, localSet, globalGet, globalSet,
    i64Const, i64Eq, i64Ne, i64LtU, i64GeU, i64ShrU, i64And,
    i32WrapI64, i64Load, i64Store, unreachable, returnOp, call, List.append]
  runtime_encoding⟩

end Project.Compiler.RuntimeEncoding
