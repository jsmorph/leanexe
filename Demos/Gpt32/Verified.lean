import Demos.Gpt32.Program
import Verified.Reflect.Command
import Verified.WGSL.Compile

namespace Demos.Gpt32.Verified

open _root_.Demos.Gpt32

verified_compile compiled := [expArray32, embed32, layerNorm32, linear32, append32, scores32,
  headMax32, headSum32, probs32, mix32, add32, geluArray32, logits32]

def expGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.expArray32.func.body).get (by decide +kernel)
def embedGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.embed32.func.body).get (by decide +kernel)
def layerNormGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.layerNorm32.func.body).get (by decide +kernel)
def linearGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.linear32.func.body).get (by decide +kernel)
def appendGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.append32.func.body).get (by decide +kernel)
def scoresGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.scores32.func.body).get (by decide +kernel)
def headMaxGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.headMax32.func.body).get (by decide +kernel)
def headSumGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.headSum32.func.body).get (by decide +kernel)
def probsGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.probs32.func.body).get (by decide +kernel)
def mixGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.mix32.func.body).get (by decide +kernel)
def addGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.add32.func.body).get (by decide +kernel)
def geluGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.geluArray32.func.body).get (by decide +kernel)
def logitsGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.logits32.func.body).get (by decide +kernel)

def expKernel : LeanExe.WGSL.Module := expGpu.module
def embedKernel : LeanExe.WGSL.Module := embedGpu.module
def layerNormKernel : LeanExe.WGSL.Module := layerNormGpu.module
def linearKernel : LeanExe.WGSL.Module := linearGpu.module
def appendKernel : LeanExe.WGSL.Module := appendGpu.module
def scoresKernel : LeanExe.WGSL.Module := scoresGpu.module
def headMaxKernel : LeanExe.WGSL.Module := headMaxGpu.module
def headSumKernel : LeanExe.WGSL.Module := headSumGpu.module
def probsKernel : LeanExe.WGSL.Module := probsGpu.module
def mixKernel : LeanExe.WGSL.Module := mixGpu.module
def addKernel : LeanExe.WGSL.Module := addGpu.module
def geluKernel : LeanExe.WGSL.Module := geluGpu.module
def logitsKernel : LeanExe.WGSL.Module := logitsGpu.module

end Demos.Gpt32.Verified
