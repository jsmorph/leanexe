import Project.SpectralKL.MatrixAccelerated
import Project.SpectralKL.Operations
import CodeLib.IEEE64.Roundoff
import Lean.Data.Json

namespace MatrixSeriesRun
open Lean Project.SpectralKL

def wordValue (w : UInt64) : ℚ := (LeanExe.IEEE64.scaledValue w : ℚ) / 2^1074

theorem wordValue_real (w : UInt64) : (wordValue w : ℝ) = CodeLib.IEEE64.value w := by
  simp only [wordValue,Rat.cast_div,Rat.cast_intCast,Rat.cast_pow,Rat.cast_ofNat,
    Operations.scaledValue_eq,CodeLib.IEEE64.value]

def readWord (j : Json) : Except String ℚ := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected a decimal binary64 word"
  if n ≥ 2^64 then throw "word outside UInt64"
  let w := n.toUInt64
  if !LeanExe.IEEE64.isFinite w then throw "nonfinite observation or ridge"
  return wordValue w

def readVector (m : Nat) (j : Json) : Except String (Fin m → ℚ) := do
  let xs ← j.getArr?
  if xs.size != m then throw "inconsistent feature count"
  let values ← xs.mapM readWord
  return fun i => values[i.val]!

def readRows (m : Nat) (j : Json) : Except String (List (Fin m → ℚ)) := do
  let rows ← j.getArr?
  if rows.isEmpty || rows.size*m > 524288 then throw "invalid sample count"
  return (← rows.mapM (readVector m)).toList

def evaluate (input : Json) : Except String Json := do
  let m ← (← input.getObjVal? "features").getNat?
  if m == 0 || m > 32 then throw "feature count must be between 1 and 32"
  let p ← readRows m (← input.getObjVal? "p")
  let q ← readRows m (← input.getObjVal? "q")
  let eta ← readWord (← input.getObjVal? "eta")
  let method ← (← input.getObjVal? "method").getStr?
  if method != "fixed" && method != "adaptive" && method != "damped" && method != "auto" && method != "preconditioned" then
    throw "unknown matrix method"
  let domainError := "outside matrix series domain: require eta > 0, sum of squared moment entries <= eta^2/4, squared mean difference <= 32*eta"
  let (z,k) ← if method == "fixed" then do
      let some z := MatrixEstimator.compute p q eta | throw domainError
      pure (z,12)
    else if method == "adaptive" then do
      let some result := MatrixEstimator.computeAdaptive p q eta | throw domainError
      pure result
    else if method == "damped" then do
      let some result := MatrixGeneral.compute p q eta | throw "require nonempty groups and eta > 0"
      pure result
    else if method == "preconditioned" then do
      let some result := MatrixAccelerated.compute p q eta | throw "require nonempty groups and eta > 0"
      pure result
    else do
      let some result := MatrixGeneral.computeAuto p q eta | throw "require nonempty groups and eta > 0"
      pure result
  let proof := if method == "fixed" then "Project.SpectralKL.MatrixEstimator.compute_correct"
    else if method == "adaptive" then "Project.SpectralKL.MatrixEstimator.computeAdaptive_correct"
    else if method == "damped" then "Project.SpectralKL.MatrixGeneral.compute_correct"
    else if method == "preconditioned" then "Project.SpectralKL.MatrixAccelerated.compute_correct"
    else "Project.SpectralKL.MatrixGeneral.computeAuto_correct"
  return Json.mkObj [("scaledScore",toJson (toString z)),
    ("scale",toJson "1000000000000"),
    ("absoluteErrorBound",toJson "1/1000000"),
    ("iterations",toJson k),("proof",toJson proof)]

end MatrixSeriesRun

def main : IO UInt32 := do
  let input ← (← IO.getStdin).getLine
  match Lean.Json.parse input >>= MatrixSeriesRun.evaluate with
  | .error e =>
      (← IO.getStderr).putStrLn e
      return 1
  | .ok result =>
      (← IO.getStdout).putStrLn result.compress
      return 0
