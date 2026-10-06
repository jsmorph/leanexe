
/-! The cases of the drone corpus.  `tests/drone/oracle.sh` appends this file to the earlier
system's `Examples/Drone/Program.lean` and runs the result natively.  With the argument `corpus`,
each output line is a terrain and the earlier system's `compute` of it, as comma-separated words
joined by `|`.  With `cases`, each line is a call of one of the earlier system's functions in the
format of `tests/modules/Cases.lean`: `drone|export|result kind|host arguments|the earlier system's
result`. -/

open Examples.Drone

def mix (i : Nat) : Nat := (i * 0x9E3779B97F4A7C15 + 12345) % 2 ^ 64

def report : List (List UInt64) :=
  [[0, 20, 80, 40, 0],
   List.replicate 15 0,
   [0, 0, 0, 20, 60, 100, 100, 100, 100, 100, 60, 20, 0, 0, 0],
   [0, 0, 10, 30, 60, 100, 130, 140, 130, 100, 60, 30, 10, 0, 0],
   [0, 0, 50, 110, 40, 0, 80, 140, 70, 0, 60, 120, 50, 0, 0]]

def special : List (List UInt64) :=
  [[], [0], [7], [1000000], [1000001], [18446744073709551615], [0, 0], [3, 9],
   [0, 1000000], [1000000, 0], [1000000, 1000000], [5, 1000001, 5], [0, 0, 1000001],
   List.replicate 64 0, List.replicate 65 0, List.replicate 64 1000000,
   List.replicate 100 3, (List.range 64).map fun i => UInt64.ofNat (i * 15625),
   (List.range 64).map fun i => UInt64.ofNat ((i % 2) * 200),
   (List.range 64).map fun i => UInt64.ofNat ((i % 2) * 1000000),
   (List.range 33).map fun i => if i == 16 then 400 else 0,
   (List.range 20).map fun i => if i % 7 == 3 then 90 else 10,
   (List.range 64).map fun i => if i == 63 then 1000001 else 0]

/-- One terrain of each length from 1 to 64, with heights below a bound that cycles through
gentle, moderate, and extreme ranges; the bound 1000001 admits every valid height. -/
def random : List (List UInt64) :=
  (List.range 64).map fun k =>
    let bound := [60, 250, 1000, 100000, 1000001][k % 5]!
    (List.range (k + 1)).map fun j => UInt64.ofNat (mix (1000 * k + j) % bound)

/-- Random walks with steps of up to 80 below or above the last height. -/
def walks : List (List UInt64) :=
  (List.range 16).map fun k =>
    ((List.range (4 * k + 4)).foldl (fun (acc : List UInt64 × Nat) j =>
      let step := mix (5000 + 100 * k + j) % 161
      let next := if acc.2 + step < 80 then 0 else acc.2 + step - 80
      (acc.1 ++ [UInt64.ofNat next], next)) ([], 200)).1

/-- Terrains with one height above 1000000. -/
def invalid : List (List UInt64) :=
  (List.range 8).map fun k =>
    (List.range (8 * k + 3)).map fun j =>
      if j == 4 * k + 1 then UInt64.ofNat (1000001 + mix (9000 + k) % 1000)
      else UInt64.ofNat (mix (9100 + 100 * k + j) % 500)

def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

def u (n : UInt64) : String := s!"i64:{n}"
def arr (xs : List UInt64) : String := s!"array-u64:{words xs}"
def line (name kind : String) (args : List String) (expected : String) : IO Unit :=
  IO.println s!"drone|{name}|{kind}|{" ".intercalate args}|{expected}"

def maxU : UInt64 := 18446744073709551615
def word (i : Nat) : UInt64 := UInt64.ofNat (mix i)
def below (n i : Nat) : UInt64 := UInt64.ofNat (mix i % n)

/-- Words at the boundaries of the planner's ranges and of `UInt64`. -/
def edges : List UInt64 :=
  [0, 1, 2, 4, 5, 24, 25, 44, 45, 99, 100, 1000000, 1000100, 1000300, 4294967295, 4294967296,
    9223372036854775808, maxU]

def scalarCases : IO Unit := do
  for a in edges do
    for b in edges do
      line "distance" "i64" [u a, u b] (toString (distance a b))
  for k in List.range 60 do
    let a := word (2 * k)
    let b := word (2 * k + 1)
    line "distance" "i64" [u a, u b] (toString (distance a b))
  for floor in edges ++ (List.range 10).map (fun k => below 1000101 (100 + k)) do
    for state in [0, 1, 4, 5, 22, 44, 45, 1000, maxU] do
      line "altitude" "i64" [u floor, u state] (toString (altitude floor state.toNat))
  for state in (List.range 50).map UInt64.ofNat ++ [1000, 4294967296, maxU] do
    line "speed" "i64" [u state] (toString (speed state.toNat))
  let roots : List UInt64 := (List.range 40).map UInt64.ofNat ++
    [65535, 65536, 65537, 4294836225, 4294836226, 4294967295, 4294967296, 4294967297,
      9223372036854775808, maxU] ++ (List.range 40).map fun k => below 4294967297 (200 + k)
  for n in roots ++ (List.range 10).map fun k => word (300 + k) do
    line "ceilSqrt" "i64" [u n] (toString (ceilSqrt n))
  for dh in (List.range 30).map UInt64.ofNat ++ edges ++ (List.range 40).map fun k => below 1000301 (400 + k) do
    line "restSeconds" "i64" [u dh] (toString (restSeconds dh))
  let speeds : List UInt64 := [0, 5, 10, 15, 20]
  for k in List.range 300 do
    let r0 := below 1000101 (1000 + 7 * k)
    let r1 := if k % 3 == 0 then r0 else below 1000101 (1001 + 7 * k)
    let z0 := r0 + below 9 (1002 + 7 * k) * 25
    let z1 := r1 + below 9 (1003 + 7 * k) * 25
    let v0 := speeds[mix (1004 + 7 * k) % 5]!
    let v1 := speeds[mix (1005 + 7 * k) % 5]!
    line "edgeTicks" "i64" [u r0, u r1, u z0, u z1, u v0, u v1]
      (toString (edgeTicks r0 r1 z0 z1 v0 v1))
  for k in List.range 300 do
    let r0 := below 400 (2000 + 7 * k)
    let r1 := below 400 (2001 + 7 * k)
    let z0 := r0 + below 9 (2002 + 7 * k) * 25
    let z1 := r1 + below 9 (2003 + 7 * k) * 25
    let v0 := speeds[mix (2004 + 7 * k) % 5]!
    let v1 := speeds[mix (2005 + 7 * k) % 5]!
    line "edgeTicks" "i64" [u r0, u r1, u z0, u z1, u v0, u v1]
      (toString (edgeTicks r0 r1 z0 z1 v0 v1))
  for k in List.range 40 do
    let w := fun j => if k % 2 == 0 then word (3000 + 6 * k + j) else below 3000 (3000 + 6 * k + j)
    line "edgeTicks" "i64" [u (w 0), u (w 1), u (w 2), u (w 3), u (w 4), u (w 5)]
      (toString (edgeTicks (w 0) (w 1) (w 2) (w 3) (w 4) (w 5)))

def choiceWords (c : Choice) : String := words [c.time, c.excess, c.parent]

/-- The rows of the earlier system's forward pass over `terrain`, each with the arguments of
`advance`. -/
def rows (terrain : Array UInt64) : List (UInt64 × UInt64 × Bool × Array UInt64 × Array UInt64) :=
  ((List.range (terrain.size - 1)).foldl (fun (acc : List _ × Array UInt64) k =>
    let i := k + 1
    let r0 := floorAt terrain (i - 1)
    let r1 := floorAt terrain i
    let last := i + 1 == terrain.size
    let next := advance r0 r1 last acc.2
    (acc.1 ++ [(r0, r1, last, acc.2, next)], next)) ([], initial)).1

def rowCases : IO Unit := do
  line "initial" "array-u64" [] (words initial.toList)
  for terrain in report ++ (random.filter (·.length ≥ 2)).take 12 do
    for (r0, r1, last, previous, next) in rows terrain.toArray do
      line "advance" "array-u64"
        [u r0, u r1, u (if last then 1 else 0), arr previous.toList, u 0] (words next.toList)
  let choices : List Choice := (List.range 120).map fun k =>
    ⟨if k % 7 == 0 then infinity else below 50 (4000 + 3 * k),
      if k % 11 == 0 then infinity else below 50 (4001 + 3 * k), below 45 (4002 + 3 * k)⟩
  for k in List.range 119 do
    let a := choices.getD k unreachable
    let b := choices.getD (k + 1) unreachable
    line "choose" "list:i64,i64,i64"
      [u a.time, u a.excess, u a.parent, u b.time, u b.excess, u b.parent] (choiceWords (choose a b))
  for k in List.range 200 do
    let r0 := below 1000101 (5000 + 4 * k)
    let r1 := if k % 4 == 0 then r0 else below 1000101 (5001 + 4 * k)
    let target := mix (5002 + 4 * k) % 45
    let source := mix (5003 + 4 * k) % 45
    let old := choices.getD (k % 120) unreachable
    let previous := (List.range 45).foldl (fun (xs : Array UInt64) s =>
      if s == source then xs ++ #[old.time, old.excess, old.parent] else xs ++ #[0, 0, 0]) #[]
    line "predecessor" "list:i64,i64,i64"
      [u r0, u r1, u old.time, u old.excess, u old.parent, u target.toUInt64, u source.toUInt64]
      (choiceWords (predecessor r0 r1 previous target source))

def main : List String → IO Unit
  | ["corpus"] =>
    for terrain in report ++ special ++ random ++ walks ++ invalid do
      IO.println s!"{words terrain}|{words (compute terrain.toArray).toList}"
  | ["cases"] => do
    scalarCases
    rowCases
  | _ => throw <| IO.userError "usage: corpus | cases"
