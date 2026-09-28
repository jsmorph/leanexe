import LeanExe.Core.LoopExamples
import Project.Core.Frontend

namespace Project.Core.LoopExamples

run_elab Frontend.compile ``LeanExe.Core.LoopExamples.sum `Project.Core.LoopExamples.sumModule
run_elab Frontend.compileState ``LeanExe.Core.LoopExamples.sumBytes `Project.Core.LoopExamples.sumBytesModule

def nestedCompiled : Compiled (arity := 1) LeanExe.Core.LoopExamples.nested :=
  (compileNative LeanExe.Core.LoopExamples.nestedCertificate).toOption.get (by decide)

def recursiveCallsCompiled : Compiled (arity := 1) LeanExe.Core.LoopExamples.recursiveCalls :=
  (compileNative LeanExe.Core.LoopExamples.recursiveCallsCertificate).toOption.get (by decide)

def recursionAfterLoopCompiled : Compiled (arity := 1) LeanExe.Core.LoopExamples.recursionAfterLoop :=
  (compileNative LeanExe.Core.LoopExamples.recursionAfterLoopCertificate).toOption.get (by decide)

theorem sum_correct (count : UInt64) (host : Wasm.HostEnv α) (store : Wasm.Store α) :
    Wasm.TerminatesWith host sumModule sumModule.entry store [.i64 count]
      (fun final values => final = store ∧
        values = [.i64 (LeanExe.Core.LoopExamples.sum count)]) :=
  sumModule.correct [count] rfl α host store

theorem sumBytes_correct (count : UInt64) (initial : ByteArray)
    (host : Wasm.HostEnv α) (store : Wasm.Store α)
    (represented : MemoryGrow.MemoryAt initial store.mem)
    (capacity : store.memoryCap sumBytesModule 0 = 65536) :
    Wasm.TerminatesWith host sumBytesModule sumBytesModule.entry store [.i64 count]
      (fun final values =>
        (MemoryGrow.MemoryAt (LeanExe.Core.LoopExamples.sumBytes count initial).2 final.mem ∧
          final.memoryCap sumBytesModule 0 = 65536) ∧
        values = [.i64 (LeanExe.Core.LoopExamples.sumBytes count initial).1]) :=
  sumBytesModule.correct [count] rfl initial α host store represented capacity

#print axioms sum_correct
#print axioms sumBytes_correct
#print axioms nestedCompiled
#print axioms recursiveCallsCompiled
#print axioms recursionAfterLoopCompiled

end Project.Core.LoopExamples
