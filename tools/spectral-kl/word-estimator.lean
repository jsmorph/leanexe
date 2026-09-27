import Project.SpectralKL.WordAccelerated
import Project.SpectralKL.Operations
import Lean.Data.Json

namespace WordEstimatorRun
open Lean Project.SpectralKL

def readRows (m : Nat) (j : Json) : Except String (List (Fin m → WordMoments.Sample)) := do
  let rows ← j.getArr?
  if rows.isEmpty || rows.size*m > 524288 then throw "invalid sample count"
  let rows ← rows.mapM fun row => do
    let xs ← row.getArr?
    if xs.size != m then throw "inconsistent feature count"
    let values ← xs.mapM fun x => do
      let n ← x.getNat?
      if h : n < 65536 then pure (⟨n,h⟩ : WordMoments.Sample)
      else throw "encoded sample outside u16"
    return fun i : Fin m => values[i.val]!
  return rows.toList

def readRidge (j : Json) : Except String ℚ := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected a decimal binary64 word"
  if n ≥ 2^64 then throw "word outside UInt64"
  let w := n.toUInt64
  if !LeanExe.IEEE64.isFinite w then throw "nonfinite ridge"
  return (LeanExe.IEEE64.scaledValue w:ℚ)/2^1074

def report (z : Int) (k : Nat) (proof : String) : Json :=
  Json.mkObj [("scaledScore",toJson (toString z)),("iterations",toJson k),
    ("absoluteErrorBound",toJson "1/1000000"),("proof",toJson proof)]

def readTotals (m : Nat) (j : Json) : Except String (WordMoments.Totals m) := do
  let xs ← j.getArr?
  if xs.size != 2*(m+m*m) then throw "invalid GPU output size"
  let words ← xs.mapM fun x => do
    let n ← x.getNat?
    if n ≥ 4294967296 then throw "GPU output is not a u32"
    return UInt32.ofNat n
  let readEntry := fun i => ({lo := words[2*i]!,hi := words[2*i+1]!} : WordMoments.Sum64)
  return ⟨MatrixPolynomial.store (fun i => readEntry i.val),
    MatrixPolynomial.store (fun i => MatrixPolynomial.store (fun k => readEntry (m+i.val*m+k.val)))⟩

/-- Inspect the exact input-derived bounds without starting the polynomial
iteration. This reports algorithm choices, not a computed score. -/
def diagnostics {m : Nat} (tp tq : WordMoments.Totals m) (np nq : Nat) (scale eta : ℚ) : Json :=
  let a := WordMoments.momentOf tp np scale
  let b := WordMoments.momentOf tq nq scale
  let M := ExactSolve.preconditioner (MatrixEstimator.matrixView a) (MatrixEstimator.matrixView b) eta
  let base := MatrixAccelerated.baseContraction (MatrixEstimator.matrixView a) (MatrixEstimator.matrixView b) eta
  let pre := MatrixPreconditioned.contraction (MatrixEstimator.matrixView a) (MatrixEstimator.matrixView b)
    (MatrixEstimator.matrixView M) eta
  Json.mkObj [("baseContractionFloor1e12",toJson (toString (MatrixEstimator.roundScore base))),
    ("preconditionedContractionFloor1e12",toJson (toString (MatrixEstimator.roundScore pre))),
    ("preconditionedContracts",toJson (decide (pre<1))),
    ("usesPreconditioner",toJson (decide (pre<base)))]

def evaluate (input : Json) : Except String Json := do
  let mode ← (← input.getObjVal? "mode").getStr?
  if mode == "shader" then return Json.mkObj [("source",toJson WordShader.kernel.source)]
  if mode != "cpu" && mode != "gpu-finish" && mode != "cpu-diagnostics" && mode != "gpu-diagnostics" then
    throw "unknown mode"
  let method ← (← input.getObjVal? "method").getStr?
  if method != "auto" && method != "preconditioned" then throw "unknown method"
  let m ← (← input.getObjVal? "features").getNat?
  if m == 0 || m > 32 then throw "feature count must be between 1 and 32"
  let scale ← (← input.getObjVal? "denominator").getNat?
  if scale == 0 then throw "denominator must be positive"
  let eta ← readRidge (← input.getObjVal? "eta")
  if eta ≤ 0 then throw "ridge must be positive"
  if mode == "gpu-finish" || mode == "gpu-diagnostics" then
    let np ← (← input.getObjVal? "np").getNat?
    let nq ← (← input.getObjVal? "nq").getNat?
    if np == 0 || nq == 0 || np*m > 524288 || nq*m > 524288 then throw "invalid sample count"
    let tp ← readTotals m (← input.getObjVal? "tp")
    let tq ← readTotals m (← input.getObjVal? "tq")
    if mode == "gpu-diagnostics" then return diagnostics tp tq np nq (scale:ℚ) eta
    if method == "preconditioned" then
      let (z,k) := WordAccelerated.finish tp tq np nq (scale:ℚ) eta
      return report z k "Project.SpectralKL.WordAccelerated.computeSource_correct"
    else
      let (z,k) := WordMoments.finish tp tq np nq (scale:ℚ) eta
      return report z k "Project.SpectralKL.WordShader.compute_correct"
  let p ← readRows m (← input.getObjVal? "p")
  let q ← readRows m (← input.getObjVal? "q")
  if mode == "cpu-diagnostics" then
    return diagnostics (WordMoments.totals p) (WordMoments.totals q) p.length q.length (scale:ℚ) eta
  if method == "preconditioned" then
    let some (z,k) := WordAccelerated.compute p q (scale:ℚ) eta | throw "invalid estimator input"
    return report z k "Project.SpectralKL.WordAccelerated.compute_correct"
  else
    let some (z,k) := WordMoments.compute p q (scale:ℚ) eta | throw "invalid estimator input"
    return report z k "Project.SpectralKL.WordMoments.compute_correct"

end WordEstimatorRun

def main : IO UInt32 := do
  let input ← (← IO.getStdin).getLine
  match Lean.Json.parse input >>= WordEstimatorRun.evaluate with
  | .error e => (← IO.getStderr).putStrLn e; return 1
  | .ok result => (← IO.getStdout).putStrLn result.compress; return 0
