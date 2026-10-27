import TestSupport.Slew.Cases

/-! The single-cone edge cases of the module `slew`: 100,000 calls of the `edgeOk` export, each
on an input of one body vector and one cone with a start attitude and a relative quaternion, with
native Lean's results.  `tests/slew/edges.sh` runs them in one host session.

The classes are random edges; cones whose limit lies within `1e-8` of the designed extremum of a
rotation, inside the rotation or near its ends; stationary points of the cosine at the start or
the end of a rotation, with `B` within and beyond `eta`; and relative quaternions whose vector
length lies near 0, near the small-angle threshold `sMin`, or near 1, with limits near the start's
cosine.  The relative quaternion of the grazing and stationary classes comes from the program's
`relative`, as in `plan`, and the other classes build it directly. -/

namespace TestSupport.Slew.Edges

open Demos.Slew (V3 Q4 edgeOk dims relative)
open TestSupport.Slew.Cases

/-- One edge: the body vector, the cone, the start attitude, and the relative quaternion. -/
structure Edge where
  b : V3
  cone : Cone
  qa : Q4
  rel : Q4

def identity : Q4 := ⟨1, 0, 0, 0⟩

/-- The input of an edge: the header of `single`, identity start and goal attitudes, which
`edgeOk` does not read, the body vector, and the cone. -/
def input (e : Edge) : Array Float :=
  pack { q0 := identity, q1 := identity, bodies := [e.b], cones := [e.cone], ways := [],
         maxEdge := 3.2 }

def flag : Gen Bool := return (← word) % 2 == 1

def random : Gen Edge := do
  let qa ← unitQuat
  let rel := turn (← unitVec) (← uniform)
  return ⟨(← unitVec), ⟨0, (← unitVec), (← between (-1) 1), (← flag)⟩, qa, rel⟩

/-- The grazing construction of `Cases.grazing`, with the extremum anywhere in the rotation and
the limit at a random distance of at most `1e-8`, `2.2e-9`, or `1.2e-9` from it. -/
def grazing : Gen Edge := do
  let n ← unitVec
  let p ← perpendicular n
  let t ← between 0.02 0.95
  let ts := (← between 0.01 0.99) * (2 * t / (1 - t * t))
  let pstar := vadd (vscale p (cosOf ts)) (vscale (vcross n p) (sinOf ts))
  let tg ← between (-0.9) 0.9
  let tb ← between (-0.9) 0.9
  let v0 := vadd (vscale p (cosOf tg)) (vscale n (sinOf tg))
  let y0 := vunit (vcross n v0)
  let qa := ofFrame v0 y0 (vcross v0 y0)
  let qb := qmul (turn n t) qa
  let extremum := cosOf tb * cosOf tg + sinOf tb * sinOf tg
  let keepIn ← flag
  let u := vscale (vadd (vscale pstar (cosOf tb)) (vscale n (sinOf tb))) (if keepIn then -1 else 1)
  let eps := (2 * (← uniform) - 1) * (← pick [1e-8, 2.2e-9, 1.2e-9])
  let c := if keepIn then -extremum - eps else extremum + eps
  return ⟨xAxis, ⟨0, u, max (-1) (min 1 c), keepIn⟩, qa, relative qa qb⟩

/-- The stationary construction of `Cases.stationary`: `u` has a component `t (n × v₀)`, so `B`
is proportional to `t`, and the limit lies `gap` beyond the start's cosine; the reversed rotation
puts the stationary point at the end. -/
def stationary : Gen Edge := do
  let qa ← unitQuat
  let n ← unitVec
  let qb := qmul (turn n (← between 0.02 0.9)) qa
  let v0 := rot qa xAxis
  let perp := vsub v0 (vscale n (vdot n v0))
  let t ← pick [-1e-6, -1e-11, -1e-12, -1e-13, 0, 1e-13, 1e-12, 1e-11, 1e-6]
  let keepIn ← flag
  let u := vunit (vadd (vadd (vscale perp (if keepIn then -1 else 1)) (vscale n 0.8))
    (vscale (vcross n v0) t))
  let f0 := vdot u v0
  let gap ← pick [2e-9, 1.2e-9, 1.1e-9, 1e-12, 0]
  let c := if keepIn then f0 - gap else f0 + gap
  let cone : Cone := ⟨0, u, max (-1) (min 1 c), keepIn⟩
  if ← flag then return ⟨xAxis, cone, qb, relative qb qa⟩
  else return ⟨xAxis, cone, qa, relative qa qb⟩

def axes : List V3 := [⟨1, 0, 0⟩, ⟨0, 1, 0⟩, ⟨0, 0, 1⟩, ⟨-1, 0, 0⟩]

/-- A relative quaternion with a vector length near 0, near `sMin`, or near 1, about a random or
a coordinate axis, and a limit within `3 s + 3e-9` of the start's cosine. -/
def angles : Gen Edge := do
  let qa ← unitQuat
  let coordinate := (← word) % 4 == 0
  let k := ((← word) % 4).toNat
  let n ← if coordinate then pure (axes.getD k xAxis) else unitVec
  let sMin := Demos.Slew.sMin
  let s ← pick [0, 1e-300, 1e-160, 1e-15, 1e-12, 1e-9, 5e-8, 0.99e-7, 0.999999e-7,
    Float.ofBits (sMin.toBits - 1), sMin, Float.ofBits (sMin.toBits + 1), 1.000001e-7, 1.01e-7,
    1e-6, 1e-3, 0.5, 1 - 1e-12, 1]
  let w := (1 - s * s).sqrt
  let rel : Q4 := ⟨w, n.x * s, n.y * s, n.z * s⟩
  let b ← unitVec
  let u ← unitVec
  let f0 := vdot u (rot qa b)
  let c := f0 + (2 * (← uniform) - 1) * (3 * s + 3e-9)
  return ⟨b, ⟨0, u, max (-1) (min 1 c), (← flag)⟩, qa, rel⟩

def many (n : Nat) (g : Gen Edge) : Gen (Array Edge) := do
  let mut out := #[]
  for _ in [0:n] do out := out.push (← g)
  return out

def classes : List (String × Array Edge) :=
  [("random", Id.run ((many 40000 random).run' 11)),
    ("grazing", Id.run ((many 30000 grazing).run' 12)),
    ("stationary", Id.run ((many 15000 stationary).run' 13)),
    ("angles", Id.run ((many 15000 angles).run' 14))]

/-- Writes the host session to `scriptPath` and native Lean's result of each call, one line
`results 0` or `results 1` per edge, to `expectedPath`, and prints each class's counts.  The
session keeps one input array, rewrites its body and cone for each edge, and releases it at the
end. -/
def write (scriptPath expectedPath : String) : IO Unit := do
  let base := input ⟨xAxis, ⟨0, xAxis, 0, false⟩, identity, identity⟩
  let d := dims base
  let dimArgs := String.join
    ([d.nb, d.nc, d.nw, d.coneOff, d.wayOff, d.total].map fun w => s!"arg-u64 {w}\n")
  let script ← IO.FS.Handle.mk scriptPath .write
  let expected ← IO.FS.Handle.mk expectedPath .write
  script.putStr s!"alloc 1 {8 * (base.size + 1)}\nwrite-u64 1 0 {base.size}\n"
  for i in [0:base.size] do
    script.putStr s!"write-u64 1 {8 * (i + 1)} {base[i]!.toBits}\n"
  for (name, edges) in classes do
    let mut accepted := 0
    for e in edges do
      let xs := input e
      let mut buf := ""
      for i in [16:xs.size] do
        buf := buf ++ s!"write-u64 1 {8 * (i + 1)} {xs[i]!.toBits}\n"
      buf := buf ++ "arg-ptr 1\n" ++ dimArgs
      for x in q4s e.qa ++ q4s e.rel do
        buf := buf ++ s!"arg-f64 {x.toBits}\n"
      script.putStr (buf ++ "call edgeOk 1\n")
      let ok := edgeOk xs d e.qa e.rel
      expected.putStrLn s!"results {if ok then 1 else 0}"
      if ok then accepted := accepted + 1
    IO.println s!"{name}: {edges.size} edges, {accepted} accepted"
  script.putStr "arg-ptr 1\ncall release 0\nstats\n"

end TestSupport.Slew.Edges
