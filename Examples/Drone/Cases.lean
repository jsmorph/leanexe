import Examples.Drone.Program
import Examples.Host

/-! The module cases of `drone`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Drone

open Examples.Host

/-- The words of a host argument `i64:N` or `array-u64:N,N`. -/
def argWords (arg : String) : List UInt64 :=
  match arg.splitOn ":" with
  | ["i64", w] => [w.toNat!.toUInt64]
  | ["array-u64", ""] => []
  | ["array-u64", ws] => (ws.splitOn ",").map (·.toNat!.toUInt64)
  | _ => []

/-- The choices whose words are `ws`, three each. -/
def choicesOf (ws : List UInt64) : Array Choice :=
  ((List.range (ws.length / 3)).map fun k => ⟨ws[3 * k]!, ws[3 * k + 1]!, ws[3 * k + 2]!⟩).toArray

def choiceWords (c : Choice) : List UInt64 := [c.time, c.excess, c.parent]

/-- The current system's result for a call of `tests/drone/cases.txt`. -/
def droneResult (name : String) (args : List (List UInt64)) : List UInt64 :=
  match name, args with
  | "distance", [[a], [b]] => [distance a b]
  | "altitude", [[floor], [state]] => [altitude floor state]
  | "speed", [[state]] => [speed state]
  | "ceilSqrt", [[n]] => [ceilSqrt n]
  | "restSeconds", [[dh]] => [restSeconds dh]
  | "edgeTicks", [[r0], [r1], [z0], [z1], [v0], [v1]] => [edgeTicks r0 r1 z0 z1 v0 v1]
  | "choose", [[t0], [e0], [p0], [t1], [e1], [p1]] => choiceWords (choose ⟨t0, e0, p0⟩ ⟨t1, e1, p1⟩)
  | "predecessor", [[r0], [r1], [t], [e], [p], [target], [source]] =>
    choiceWords (predecessor r0 r1 ⟨t, e, p⟩ target source)
  | "advance", [[r0], [r1], [last], previous, [base]] =>
    (advance r0 r1 (last == 1) (choicesOf previous) base).toList.flatMap choiceWords
  | "initial", [] => initial.toList.flatMap choiceWords
  | _, _ => []

/-- The drone calls of `tests/drone/cases.txt`, whose expected results are the earlier system's, and
the terrains of `tests/drone/corpus.txt`, each with the current system's result. -/
def droneCases : IO Unit := do
  for case in (← IO.FS.lines "tests/drone/cases.txt").filter (!·.isEmpty) do
    let [m, name, kind, args, _] := case.splitOn "|" | throw <| IO.userError s!"bad case: {case}"
    let argv := if args.isEmpty then [] else args.splitOn " "
    line m name kind argv (words (droneResult name (argv.map argWords)))
  for case in (← IO.FS.lines "tests/drone/corpus.txt").filter (!·.isEmpty) do
    let [terrain, _] := case.splitOn "|" | throw <| IO.userError s!"bad terrain: {case}"
    let heights := argWords s!"array-u64:{terrain}"
    line "drone" "compute" "array-u64" [arrU heights]
      (words (Examples.Drone.compute heights.toArray).toList)

def cases : IO Unit := do
  droneCases

end Examples.Drone
