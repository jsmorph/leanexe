import Verified.Reflect.Command
import Verified.WGSL.Compile

namespace Verified.Examples.Wgsl

def scale (gain : Float32) (xs : Array Float32) : Array Float32 :=
  LeanExe.build xs.size.toUInt64 fun i => gain * xs[i.toNat]!

def branchSum (xs : Array Float32) (n limit : UInt64) : Array Float32 :=
  LeanExe.build n fun i =>
    if i < limit then
      let sum := LeanExe.loop limit 0.0 fun j acc => acc + xs[j.toNat]!
      sum * xs[i.toNat]!
    else
      let x := xs[i.toNat]!
      (-x)

def flags (xs : Array Bool) (n : UInt64) (invert : Bool) : Array Bool :=
  LeanExe.build n fun i => if invert then !xs[i.toNat]! else xs[i.toNat]!

def wordScan (xs : Array UInt64) (n : UInt64) : Array UInt64 :=
  LeanExe.build n fun i =>
    let first := xs[i.toNat]!
    LeanExe.loop (i % 4) first fun j acc => acc * 3 + xs[j.toNat]!

def roundRoot (xs : Array Float32) : Array Float32 :=
  LeanExe.build xs.size.toUInt64 fun i => (LeanExe.Float32.nearest xs[i.toNat]!).sqrt

verified_compile compiled := [scale, branchSum, flags, wordScan, roundRoot]

def scaleGpu := (Verified.WGSL.compile (e := .float32) compiled.scale.func.body).get (by decide +kernel)
def branchGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.branchSum.func.body).get (by decide +kernel)
def flagsGpu := (Verified.WGSL.compile (e := .bool) compiled.flags.func.body).get (by decide +kernel)
def wordsGpu := (Verified.WGSL.compile (e := .word) compiled.wordScan.func.body).get (by decide +kernel)
def rootsGpu :=
  (Verified.WGSL.compile (e := .float32) compiled.roundRoot.func.body).get (by decide +kernel)

def verifiedScaleKernel : LeanExe.WGSL.Module := scaleGpu.module
def verifiedBranchKernel : LeanExe.WGSL.Module := branchGpu.module
def verifiedFlagsKernel : LeanExe.WGSL.Module := flagsGpu.module
def verifiedWordsKernel : LeanExe.WGSL.Module := wordsGpu.module
def verifiedRootsKernel : LeanExe.WGSL.Module := rootsGpu.module

end Verified.Examples.Wgsl
