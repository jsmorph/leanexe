import LeanExe.Core.StateExamples
import Project.Core.MemoryCompiler

namespace Project.Core.StateExamples

open LeanExe.Core.StateExamples

def byteSumCompiled : MemoryCompiled (arity := 1) byteSum :=
  (compileMemory byteSumCertificate).toOption.get (by decide)

def copyCompiled : MemoryCompiled (arity := 2) copy :=
  (compileMemory copyCertificate).toOption.get (by decide)

def allocationCompiled : MemoryCompiled (arity := 1) allocation :=
  (compileMemory allocationCertificate).toOption.get (by decide)

def recursiveWriteCompiled : MemoryCompiled (arity := 3) recursiveWrite :=
  (compileMemory recursiveWriteCertificate).toOption.get (by decide)

def mainCompiled : MemoryCompiled (arity := 0) LeanExe.Core.StateExamples.main :=
  (compileMemory mainCertificate).toOption.get (by decide)

def updateByteCompiled : MemoryCompiled (arity := 1) updateByte :=
  (compileMemory updateByteCertificate).toOption.get (by decide)

/-- The result and every accessible output byte agree with the native state computation. -/
theorem recursiveWrite_correct (count address value : UInt64) (initial : ByteArray)
    (host : Wasm.HostEnv α) (store : Wasm.Store α)
    (represented : MemoryGrow.MemoryAt initial store.mem)
    (capacity : store.memoryCap recursiveWriteCompiled.target 0 = 65536) :
    Wasm.TerminatesWith host recursiveWriteCompiled.target recursiveWriteCompiled.entry store
      [.i64 value, .i64 address, .i64 count]
      (fun final values =>
        (MemoryGrow.MemoryAt (recursiveWrite count address value initial).2 final.mem ∧
          final.memoryCap recursiveWriteCompiled.target 0 = 65536) ∧
        values = [.i64 (recursiveWrite count address value initial).1]) :=
  recursiveWriteCompiled.correct [count, address, value] rfl initial α host store represented capacity

/-- The generated module's normal initial memory satisfies the representation. -/
theorem recursiveWrite_initial [Inhabited α] (count address value : UInt64)
    (host : Wasm.HostEnv α) :
    Wasm.TerminatesWith host recursiveWriteCompiled.target recursiveWriteCompiled.entry
      recursiveWriteCompiled.target.initialStore [.i64 value, .i64 address, .i64 count]
      (fun final values =>
        (MemoryGrow.MemoryAt
          (recursiveWrite count address value (LeanExe.Core.Memory.zeroBytes (16 * 65536))).2 final.mem ∧
          final.memoryCap recursiveWriteCompiled.target 0 = 65536) ∧
        values = [.i64 (recursiveWrite count address value
          (LeanExe.Core.Memory.zeroBytes (16 * 65536))).1]) := by
  apply recursiveWrite_correct
  · exact (initial_memory_represents recursiveWriteCertificate.source
      [{ name := "main", funcIdx := recursiveWriteCertificate.entry }]).1
  · exact (initial_memory_represents recursiveWriteCertificate.source
      [{ name := "main", funcIdx := recursiveWriteCertificate.entry }]).2

#print axioms recursiveWrite_correct
#print axioms recursiveWrite_initial

end Project.Core.StateExamples
