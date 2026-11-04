import Examples.Binary32.Compiled
import Verified.PTX.Compile

/-! The PTX kernels that `Verified.PTX.compile` translates from the reflected bodies of `scale32`,
`axpyArray32`, `matVec32`, and `condMix32`, and their launch theorems under the PTX memory model.
Each theorem comes from `Compiled.executions_eq` with the generated `denote_eq`. -/

namespace Examples.Binary32

open Verified.PTX (LaunchMeets)

def scale32Ptx :=
  (Verified.PTX.compile (e := .float32) compiled.scale32.func.body).get (by decide +kernel)
def axpyArray32Ptx :=
  (Verified.PTX.compile (e := .float32) compiled.axpyArray32.func.body).get (by decide +kernel)
def matVec32Ptx :=
  (Verified.PTX.compile (e := .float32) compiled.matVec32.func.body).get (by decide +kernel)
def condMix32Ptx :=
  (Verified.PTX.compile (e := .float32) compiled.condMix32.func.body).get (by decide +kernel)

def ptxScale32Kernel : LeanExe.PTX.Module := scale32Ptx.module
def ptxAxpyArray32Kernel : LeanExe.PTX.Module := axpyArray32Ptx.module
def ptxMatVec32Kernel : LeanExe.PTX.Module := matVec32Ptx.module
def ptxCondMix32Kernel : LeanExe.PTX.Module := condMix32Ptx.module

theorem scale32_executions (a : Float32) (x : Array Float32)
    (fits : scale32Ptx.spec.Fits (scale32Ptx.args (.cons a (.cons x .nil))) x.size)
    (ys : Array UInt64) (hys : ys.size = x.size) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : x.size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchMeets ptxScale32Kernel (scale32Ptx.args (.cons a (.cons x .nil))) x.size ys blocks block
      ((scale32 a x).map fun v => v.toBits.toUInt64) :=
  scale32Ptx.executions_eq _ (.cons a (.cons x .nil)) _ (compiled.scale32.denote_eq a x) x.size
    fits ys hys blocks block hb hb32 hbl hcover hthreads

theorem axpyArray32_executions (a : Float32) (x y : Array Float32)
    (fits : axpyArray32Ptx.spec.Fits (axpyArray32Ptx.args (.cons a (.cons x (.cons y .nil))))
      x.size)
    (ys : Array UInt64) (hys : ys.size = x.size) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : x.size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchMeets ptxAxpyArray32Kernel (axpyArray32Ptx.args (.cons a (.cons x (.cons y .nil))))
      x.size ys blocks block ((axpyArray32 a x y).map fun v => v.toBits.toUInt64) :=
  axpyArray32Ptx.executions_eq _ (.cons a (.cons x (.cons y .nil))) _
    (compiled.axpyArray32.denote_eq a x y) x.size fits ys hys blocks block hb hb32 hbl hcover
    hthreads

theorem matVec32_executions (m v : Array Float32) (rows cols : UInt64)
    (fits : matVec32Ptx.spec.Fits
      (matVec32Ptx.args (.cons m (.cons v (.cons rows (.cons cols .nil))))) rows.toNat)
    (ys : Array UInt64) (hys : ys.size = rows.toNat) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : rows.toNat ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchMeets ptxMatVec32Kernel
      (matVec32Ptx.args (.cons m (.cons v (.cons rows (.cons cols .nil))))) rows.toNat ys blocks
      block ((matVec32 m v rows cols).map fun v => v.toBits.toUInt64) :=
  matVec32Ptx.executions_eq _ (.cons m (.cons v (.cons rows (.cons cols .nil)))) _
    (compiled.matVec32.denote_eq m v rows cols) rows.toNat fits ys hys blocks block hb hb32 hbl
    hcover hthreads

theorem condMix32_executions (x : Array Float32) (lo hi : Float32) (n : UInt64)
    (fits : condMix32Ptx.spec.Fits
      (condMix32Ptx.args (.cons x (.cons lo (.cons hi (.cons n .nil))))) x.size)
    (ys : Array UInt64) (hys : ys.size = x.size) (blocks block : Nat) (hb : 0 < block)
    (hb32 : block < 2 ^ 32) (hbl : blocks < 2 ^ 32) (hcover : x.size ≤ blocks * block)
    (hthreads : blocks * block < 2 ^ 60) :
    LaunchMeets ptxCondMix32Kernel
      (condMix32Ptx.args (.cons x (.cons lo (.cons hi (.cons n .nil))))) x.size ys blocks block
      ((condMix32 x lo hi n).map fun v => v.toBits.toUInt64) :=
  condMix32Ptx.executions_eq _ (.cons x (.cons lo (.cons hi (.cons n .nil)))) _
    (compiled.condMix32.denote_eq x lo hi n) x.size fits ys hys blocks block hb hb32 hbl hcover
    hthreads

end Examples.Binary32

#print axioms Examples.Binary32.scale32_executions
#print axioms Examples.Binary32.axpyArray32_executions
#print axioms Examples.Binary32.matVec32_executions
#print axioms Examples.Binary32.condMix32_executions
