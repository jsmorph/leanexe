import Demos.Gate.Assignment
import TestSupport.Host

/-! Cases of the module `assignment`.  `solve` is the unproved solver, the Hungarian method with
potentials in the form of e-maxx's assignment algorithm, which returns an optimal assignment and
potentials `u`, `v` with `u i + v j ≤ c i j` for every pair and equality on the assignment's
pairs.  A forbidden pair enters the solver with the cost `2⁵⁰`.  `instances` draws random costs
from a linear congruential generator, and `certificates` gives, for each instance, the solver's
certificate and its mutations.  `cases` prints the module cases for `tests/verified/run.sh`, and
`bits` prints, for `tests/gate/assignment.py`, one line per call:
`check label n c perm u v status row col`, with each array as comma-separated words. -/

namespace TestSupport.Gate.AssignmentCases

open TestSupport.Host Demos.Gate.Assignment

/-- The word of the forbidding cost. -/
def mark : Int := 9223372036854775807

/-- The solver's cost of a forbidden pair. -/
def big : Int := 2 ^ 50

/-- An optimal assignment of the `n × n` costs `a` and its potentials: row `i` takes column
`perm[i]`, and `u[i] + v[j] ≤ a i j` with equality on the assignment's pairs. -/
def solve (n : Nat) (a : Nat → Nat → Int) : Array Nat × Array Int × Array Int := Id.run do
  let inf : Int := 2 ^ 62
  let mut u : Array Int := Array.replicate (n + 1) 0
  let mut v : Array Int := Array.replicate (n + 1) 0
  let mut p : Array Nat := Array.replicate (n + 1) 0
  let mut way : Array Nat := Array.replicate (n + 1) 0
  for i in [1:n + 1] do
    p := p.set! 0 i
    let mut j0 := 0
    let mut minv : Array Int := Array.replicate (n + 1) inf
    let mut used : Array Bool := Array.replicate (n + 1) false
    for _ in [0:n + 1] do
      used := used.set! j0 true
      let i0 := p[j0]!
      let mut delta := inf
      let mut j1 := 0
      for j in [1:n + 1] do
        if !used[j]! then
          let cur := a (i0 - 1) (j - 1) - u[i0]! - v[j]!
          if cur < minv[j]! then
            minv := minv.set! j cur
            way := way.set! j j0
          if minv[j]! < delta then
            delta := minv[j]!
            j1 := j
      for j in [0:n + 1] do
        if used[j]! then
          u := u.set! p[j]! (u[p[j]!]! + delta)
          v := v.set! j (v[j]! - delta)
        else
          minv := minv.set! j (minv[j]! - delta)
      j0 := j1
      if p[j0]! == 0 then break
    for _ in [0:n + 1] do
      let j1 := way[j0]!
      p := p.set! j0 p[j1]!
      j0 := j1
      if j0 == 0 then break
  let mut perm : Array Nat := Array.replicate n 0
  for j in [1:n + 1] do
    perm := perm.set! (p[j]! - 1) (j - 1)
  return (perm, (u.extract 1 (n + 1)), (v.extract 1 (n + 1)))

/-- The generator of the instances. -/
def next (s : Nat) : Nat := (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- An instance of `n` rows with costs from `-bound` to `bound`, each pair forbidden with
probability `forbid/16`, from the seed `seed`. -/
def instance' (n bound forbid seed : Nat) : Array Int := Id.run do
  let mut s := next (seed + 1)
  let mut c : Array Int := #[]
  for _ in [0:n * n] do
    s := next s
    let x : Nat := (s / 2 ^ 20) % (2 * bound + 1)
    s := next s
    let f : Nat := (s / 2 ^ 40) % 16
    c := c.push (if f < forbid then mark else (x : Int) - (bound : Int))
  return c

/-- A labeled call: the costs, the assignment, and the certificate. -/
structure Call where
  label : String
  c : Array Int
  perm : Array Nat
  u : Array Int
  v : Array Int

def words (xs : Array Int) : List UInt64 := xs.toList.map fun x => (Int64.ofInt x).toUInt64

def run (k : Call) : Check :=
  check (k.c.map Int64.ofInt) (k.perm.map UInt64.ofNat) (k.u.map Int64.ofInt) (k.v.map Int64.ofInt)

/-- The solver's certificate of the costs `c` and its mutations. -/
def certificates (c : Array Int) : List Call :=
  let n := Nat.sqrt c.size
  let a := fun i j => let w := c[i * n + j]!; if w == mark then big else w
  let (perm, u, v) := solve n a
  let base : Call := ⟨"solver", c, perm, u, v⟩
  let mutated : List Call :=
    [⟨"raised", c, perm, u.modify 0 (· + 1), v⟩,
     ⟨"shifted", c, perm, (u.modify 0 (· + 1)).modify (n - 1) (· - 1), v⟩,
     ⟨"range", c, perm, u.set! (n - 1) (2 ^ 62), v⟩,
     ⟨"column", c, perm.set! 0 n, u, v⟩,
     ⟨"forbidden", c.set! (perm[0]!) mark, perm, u, v⟩] ++
    (if n ≥ 2 then
      [⟨"swapped", c, (perm.set! 0 perm[1]!).set! 1 perm[0]!, u, v⟩,
       ⟨"repeated", c, perm.set! 1 perm[0]!, u, v⟩,
       ⟨"tight-repeated", c.set! (1 * n + perm[0]!) (u[1]! + v[perm[0]!]!), perm.set! 1 perm[0]!,
         u, v⟩,
       ⟨"violated", c.set! (1 * n + perm[0]!) (u[1]! + v[perm[0]!]! - 1), perm, u, v⟩]
    else [])
  base :: mutated

/-- Instances: sizes 1 to 9, 16, 64, and 100, costs of magnitude up to 100 and up to `2⁴⁰`,
negative costs, and forbidden pairs with probabilities 0, 1/8, and 3/4. -/
def instances : List (Array Int) :=
  (List.range 9).flatMap (fun m =>
    [instance' (m + 1) 100 0 m, instance' (m + 1) (2 ^ 40) 0 (m + 50),
      instance' (m + 1) 100 2 (m + 100), instance' (m + 1) 1000 12 (m + 150)]) ++
  [instance' 16 100 0 7, instance' 16 (2 ^ 40) 2 8, instance' 64 1000 2 9,
    instance' 100 (2 ^ 40) 0 10]

/-- Calls that the mutations of random instances do not give: an all-zero instance with a
repeated column, whose pairs are all tight, and the instance `[[0, 5], [0, 5]]` with a repeated
column and a certificate tight on its pairs, whose cost 0 lies below the optimum 5; sizes outside
the range; dual values at the ends of the range and costs near `±2⁶³`; a row whose pairs are all
forbidden; a repeated column in rows that are not adjacent; a repeated column after a row that is
not tight, which gives status 5; and a violated pair at `t = 0` before a repeated column at
`t = 1`, which gives status 4. -/
def special : List Call :=
  [⟨"repeated", #[0, 0, 0, 0, 0, 0, 0, 0, 0], #[0, 0, 1], #[0, 0, 0], #[0, 0, 0]⟩,
   ⟨"repeated", #[0, 5, 0, 5], #[0, 0], #[0, 0], #[0, 5]⟩,
   ⟨"empty", #[], #[], #[], #[]⟩,
   ⟨"sizes", #[1, 2, 3], #[0, 1], #[0, 0], #[0, 0]⟩,
   ⟨"sizes", #[1, 2, 3, 4], #[0, 1], #[0], #[0, 0]⟩,
   ⟨"ends", #[2 ^ 62], #[0], #[2 ^ 62 - 1], #[1]⟩,
   ⟨"ends", #[-2 ^ 62], #[0], #[-(2 ^ 62) + 1], #[-1]⟩,
   ⟨"range", #[-2 ^ 62 - 1], #[0], #[-(2 ^ 62)], #[-1]⟩,
   ⟨"forbidden", #[mark], #[0], #[0], #[0]⟩,
   ⟨"forbidden", #[1, 2, mark, mark], #[0, 1], #[0, 0], #[1, 2]⟩,
   ⟨"ends", #[2 ^ 63 - 2], #[0], #[2 ^ 62 - 1], #[2 ^ 62 - 1]⟩,
   ⟨"ends", #[-(2 ^ 63)], #[0], #[-(2 ^ 62) + 1], #[-(2 ^ 62) + 1]⟩,
   ⟨"duplicate", #[0, 0, 0, 0, 0, 0, 0, 0, 0], #[1, 2, 1], #[0, 0, 0], #[0, 0, 0]⟩,
   ⟨"order", #[0, 0, 5, 0], #[0, 0], #[0, 0], #[0, 0]⟩,
   ⟨"order", #[-1, 0, 0, 0], #[1, 1], #[0, 0], #[0, 0]⟩]

def calls : List Call := (instances.flatMap certificates) ++ special

def render (xs : Array Int) : String := ",".intercalate ((words xs).map toString)

/-- The module cases omit the instance of size 100, whose costs exceed the length of one argument
on the host's command line. -/
def cases : IO Unit := do
  for k in calls.filter (·.c.size ≤ 4096) do
    let r := run k
    line "assignment" "check" "list:i64,i64,i64"
      [arrU (words k.c), arrU (k.perm.toList.map UInt64.ofNat), arrU (words k.u), arrU (words k.v)]
      s!"{r.status} {r.row} {r.col}"

def bits : IO Unit := do
  for k in calls do
    let r := run k
    IO.println s!"check {k.label} {k.perm.size} {render k.c} {render (k.perm.map Int.ofNat)} {render k.u} {render k.v} {r.status} {r.row} {r.col}"

end TestSupport.Gate.AssignmentCases
