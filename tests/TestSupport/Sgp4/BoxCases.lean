import Demos.Sgp4.Box
import TestSupport.Sgp4.Cases

/-! Cases of the enclosing SGP4 module.  `cases` prints the module cases of `sgp4BoxAround` for
`tests/verified/run.sh`.  `boxes` reads lines of the bit patterns `n e incl node argp m bstar t`
and prints the status and the bit patterns of the twelve endpoints that `sgp4BoxAround` returns,
for `tests/sgp4/reference.py`. -/

namespace TestSupport.Sgp4.BoxCases

open TestSupport.Host Demos.Sgp4 Library.Numerics.Interval

def interval (i : Interval) : String := s!"{i.status} {i.lo.toBits} {i.hi.toBits}"

def boxText (b : Box) : String :=
  s!"{b.status} {interval b.x} {interval b.y} {interval b.z} {interval b.vx} {interval b.vy} {interval b.vz}"

def boxKind : String :=
  "list:i64," ++ ",".intercalate (List.replicate 6 "i64,f64,f64")

def cases : IO Unit := do
  for (n, e, incl, node, argp, m, bstar) in TestSupport.Sgp4.Cases.elements do
    for t in TestSupport.Sgp4.Cases.times do
      line "sgp4box" "sgp4BoxAround" boxKind [fl n, fl e, fl incl, fl node, fl argp, fl m, fl bstar, fl t]
        (boxText (sgp4BoxAround n e incl node argp m bstar t))

partial def boxes : IO Unit := do
  let stdin ← IO.getStdin
  let rec go : IO Unit := do
    let text ← stdin.getLine
    if text.isEmpty then return
    let words := (text.trim.splitOn " ").filterMap String.toNat?
    match words.map fun w => Float.ofBits (UInt64.ofNat w) with
    | [n, e, incl, node, argp, m, bstar, t] =>
      IO.println (boxText (sgp4BoxAround n e incl node argp m bstar t))
    | _ => throw (IO.userError s!"expected eight words: {text}")
    go
  go

end TestSupport.Sgp4.BoxCases
