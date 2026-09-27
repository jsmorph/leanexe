import Project.SpectralKL.ScalarEstimator
import Lean.Data.Json

open Lean LeanExe.Examples.SpectralKL

def readWord (j : Json) : Except String UInt64 := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected a decimal binary64 word"
  if n ≥ 2^64 then throw "word outside UInt64"
  return n.toUInt64

def evaluate (input : Json) : Except String Json := do
  let p ← (← (← input.getObjVal? "p").getArr?).mapM readWord
  let q ← (← (← input.getObjVal? "q").getArr?).mapM readWord
  let eta ← readWord (← input.getObjVal? "eta")
  let result := fromBoundedSamples p q eta
  if result.status != 0 then throw "samples outside the estimator's input domain"
  return Json.mkObj [("bits",toJson (toString result.bits))]

def main : IO UInt32 := do
  let input ← (← IO.getStdin).getLine
  match Json.parse input >>= evaluate with
  | .error e =>
      (← IO.getStderr).putStrLn e
      return 1
  | .ok result =>
      (← IO.getStdout).putStrLn result.compress
      return 0
