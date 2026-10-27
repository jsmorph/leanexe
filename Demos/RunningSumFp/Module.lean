import Demos.RunningSumFp.Wasi
import Verified.Wasi.ProcessCode

namespace Demos.RunningSumFp

open Verified Verified.Wasi

def stateTy : Ty :=
  .pair .float (.pair (.array .word) (.pair .bytes (.pair .word
    (.pair .bytes (.elem (.prod .word .bool))))))

def entry : ProcessEntry [io.begin.func.sig, io.step.func.sig, io.readStep.func.sig, io.writeStep.func.sig] :=
  { state := stateTy
    beginName := "begin"
    stepName := "step"
    begin := io.begin.callee
    step := io.step.callee }

def module : Wasm.Module := compileProcess io.pure.module io.program entry io.literalPool

theorem stackFits : StackFits io.pure.module io.program
    (frameBytes (entry.function io.pure.module 0).locals.length) := by
  decide +kernel

theorem calls : CostEffectCalls io.pure.module module
    (Resource.PureContext.ofProg io.pure.program io.pure.funs) io.program io.literalPool :=
  io.program.correctIn
    (compileProcess_base io.program entry io.literalPool
      (compileWith_runtime io.pure.program io.pure.tables io.pure.wrappers io.literalPool)
      io.profile
      (compiled_pure_calls io.pure.program io.pure.funs io.pure.meaning io.pure.tables
        io.pure.wrappers io.literalPool io.pure_covered) io.pool_apart)
    Wasm.HostEnv.empty (compileProcess_functionsIn io.pure.module io.program entry io.literalPool)
    io.ready io.effects_covered

run_cmd Verified.Wasi.Reflect.emitValidity `command ``module
run_cmd Verified.Wasi.Reflect.emitEncoding `command ``module #[] (some ``command.validity)

end Demos.RunningSumFp
