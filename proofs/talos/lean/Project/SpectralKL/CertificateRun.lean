import Project.SpectralKL.CertificateFast
import Project.SpectralKL.Operations
import CodeLib.IEEE64.Roundoff
import Lean.Data.Json

namespace Project.SpectralKL.CertificateRun
open Lean Certificate Samples

def wordValue (word : UInt64) : ℚ :=
  (LeanExe.IEEE64.scaledValue word : ℚ) / (2^1074 : ℚ)

theorem wordValue_real (word : UInt64) :
    (wordValue word : ℝ) = CodeLib.IEEE64.value word := by
  simp only [wordValue, Rat.cast_div, Rat.cast_intCast, Rat.cast_pow,
    Rat.cast_ofNat, Operations.scaledValue_eq, CodeLib.IEEE64.value]

def readWord (j : Json) : Except String ℚ := do
  let s ← j.getStr?
  let some n := s.toNat? | throw "expected a decimal binary64 bit-pattern string"
  if n ≥ 2^64 then throw "binary64 word outside UInt64"
  let word := n.toUInt64
  if !LeanExe.IEEE64.isFinite word then throw "nonfinite value in checker input"
  return wordValue word

def readVector (m : Nat) (j : Json) : Except String (Fin m → ℚ) := do
  let entries ← j.getArr?
  if entries.size != m then throw "candidate vector has the wrong dimension"
  let values ← entries.mapM readWord
  return fun i => values[i.val]!

def readRows (m : Nat) (j : Json) : Except String (List (Fin m → ℚ)) := do
  let rows ← j.getArr?
  if rows.isEmpty || rows.size*m > 524288 then throw "invalid observation count"
  return (← rows.mapM (readVector m)).toList

def readCells (m : Nat) (j : Json) : Except String (List (ℚ × (Fin m → ℚ))) := do
  let cells ← j.getArr?
  if cells.isEmpty || cells.size > 4096 then throw "invalid interval count"
  let parsed ← cells.mapM fun c => do
    let endpoint ← readWord (← c.getObjVal? "end")
    let x ← readVector m (← c.getObjVal? "x")
    return (endpoint,x)
  return parsed.toList

def checkJson (input : Json) : Except String Json := do
  let m ← (← input.getObjVal? "features").getNat?
  if m == 0 || m > 32 then throw "feature count must be between 1 and 32"
  let p ← readRows m (← input.getObjVal? "p")
  let q ← readRows m (← input.getObjVal? "q")
  let eta ← readWord (← input.getObjVal? "eta")
  let score ← readWord (← input.getObjVal? "score")
  let tolerance ← readWord (← input.getObjVal? "tolerance")
  let cells ← readCells m (← input.getObjVal? "cells")
  let some (checked,bound) := Fast.certify p q eta score tolerance cells |
    throw "score rejected: invalid partition or requested error bound not established"
  return Json.mkObj [
    ("accepted",toJson true),
    ("score",toJson (toString checked.score)),
    ("lower",toJson (toString bound.lower)),
    ("upper",toJson (toString bound.upper)),
    ("absoluteTolerance",toJson (toString tolerance)),
    ("theorem",toJson "Project.SpectralKL.Certificate.accepts_sound")]

end Project.SpectralKL.CertificateRun

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: CertificateRun.lean request.json")
  let input ← IO.FS.readFile path
  match Lean.Json.parse input >>= Project.SpectralKL.CertificateRun.checkJson with
  | .error e =>
      (← IO.getStderr).putStrLn e
      return 1
  | .ok result =>
      (← IO.getStdout).putStrLn result.compress
      return 0

#print axioms Project.SpectralKL.CertificateRun.wordValue_real
