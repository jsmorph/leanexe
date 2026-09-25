/-!
An ideal point-mass autopilot, with an exact shortest-path search over a finite
motion-primitive graph. See docs/drone.md for units, interpolation, clearance,
optimality scope, and the UInt64 datum convention. No hardware model is used.
-/
namespace LeanExe.Examples.Drone

def stateCount : Nat := 45
def infinity : UInt64 := 1000000000000

def distance (a b : UInt64) : UInt64 :=
  if a ≥ b then a - b else b - a

def floorAt (terrain : Array UInt64) (i : Nat) : UInt64 :=
  terrain[i]! + if i == 0 || i + 1 == terrain.size then 0 else 100

def altitude (floor : UInt64) (state : Nat) : UInt64 :=
  floor + (state / 5).toUInt64 * 25

def speed (state : Nat) : UInt64 := (state % 5).toUInt64 * 5

-- Explicit fuel makes the interval invariant available to source proofs.
def sqrtSearch : Nat → UInt64 → UInt64 → UInt64 → UInt64
  | 0, _, lo, _ => lo
  | fuel + 1, n, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      if mid * mid < n then sqrtSearch fuel n (mid + 1) hi
      else sqrtSearch fuel n lo mid
    else lo

-- Binary search, bounded independently of the data. Called only with n < 2^32.
def ceilSqrt (n : UInt64) : UInt64 := sqrtSearch 17 n 0 65536

-- For a rest-to-rest segment both coordinates use 3s^2 - 2s^3.
-- Smallest whole-second duration satisfying |vx|<=20, |ax|<=1,
-- |vz|<=20, |az|<=4. The horizontal acceleration bound gives T>=25.
def restSeconds (dh : UInt64) : UInt64 :=
  max 25 (max ((3 * dh + 39) / 40) (ceilSqrt ((3 * dh + 1) / 2)))

-- Zero means infeasible; positive values are exact ticks (840 ticks/second).
-- Inputs have already been bounded by compute, and z0>=r0, z1>=r1.
def edgeTicks (r0 r1 z0 z1 u v : UInt64) : UInt64 := Id.run do
  let dh := distance z0 z1
  let total := u + v
  if total == 0 then
    return 840 * restSeconds dh
  if distance (u * u) (v * v) > 200 then return 0
  if 3 * dh * total > 8000 then return 0
  if 6 * dh * total * total > 160000 then return 0
  -- Nonnegative Bernstein coefficients certify the entire clearance curve.
  if r1 ≥ r0 then
    if 3 * total * (z0 - r0) < 2 * u * (r1 - r0) then return 0
  else
    if 3 * total * (z1 - r1) < 2 * v * (r0 - r1) then return 0
  return 33600 / (total / 5)

structure Choice where
  time : UInt64
  excess : UInt64
  parent : UInt64
  deriving DecidableEq, Repr

def unreachable : Choice := ⟨infinity, infinity, 0⟩

-- Strict improvement preserves ascending-source tie breaking.
def choose (incumbent candidate : Choice) : Choice :=
  if candidate.time < incumbent.time ∨
      (candidate.time = incumbent.time ∧ candidate.excess < incumbent.excess)
  then candidate else incumbent

def predecessor (r0 r1 : UInt64) (previous : Array UInt64)
    (target source : Nat) : Choice :=
  let old := previous[3*source]!
  let z1 := altitude r1 target
  let dt := edgeTicks r0 r1 (altitude r0 source) z1 (speed source) (speed target)
  if old < infinity ∧ dt > 0 then
    ⟨old+dt, previous[3*source+1]!+(z1-r1), source.toUInt64⟩
  else unreachable

def scanPredecessors : Nat → Nat → UInt64 → UInt64 → Array UInt64 → Nat → Choice → Choice
  | 0, _, _, _, _, _, best => best
  | count+1, source, r0, r1, previous, target, best =>
    scanPredecessors count (source+1) r0 r1 previous target
      (choose best (predecessor r0 r1 previous target source))

def bestPredecessor (count : Nat) (r0 r1 : UInt64) (previous : Array UInt64)
    (target : Nat) : Choice :=
  scanPredecessors count 0 r0 r1 previous target unreachable

def advanceLoop : Nat → Nat → UInt64 → UInt64 → Bool → Array UInt64 → Array UInt64 → Array UInt64
  | 0, _, _, _, _, _, row => row
  | count+1, target, r0, r1, last, previous, row =>
    let best := if !last || target == 0 then
      bestPredecessor stateCount r0 r1 previous target else unreachable
    advanceLoop count (target+1) r0 r1 last previous
      (((row.push best.time).push best.excess).push best.parent)

-- A row packs [time, excess, parent] for each state into one owned array.
def advance (r0 r1 : UInt64) (last : Bool) (previous : Array UInt64)
    : Array UInt64 := advanceLoop stateCount 0 r0 r1 last previous #[]

def initial : Array UInt64 := Id.run do
  let mut row : Array UInt64 := #[]
  for state in [:stateCount] do
    let cost := if state == 0 then 0 else infinity
    row := ((row.push cost).push cost).push 0
  return row

-- Named tail-recursive boundaries for source correctness proofs.
def validHeights : Nat → Array UInt64 → Bool
  | 0, _ => true
  | count+1, terrain =>
    if terrain[count]! > 1000000 then false else validHeights count terrain

def appendParents : Nat → Nat → Array UInt64 → Array UInt64 → Array UInt64
  | 0, _, _, history => history
  | count+1, state, layer, history =>
    appendParents count (state+1) layer (history.push layer[3*state+2]!)

def buildHistory : Nat → Nat → Array UInt64 → Array UInt64 → Array UInt64 → Array UInt64
  | 0, _, _, _, history => history
  | count+1, i, terrain, previous, history =>
    let layer := advance (floorAt terrain (i-1)) (floorAt terrain i)
      (i+1 == terrain.size) previous
    buildHistory count (i+1) terrain layer (appendParents stateCount 0 layer history)

def unwind : Nat → Nat → Nat → Array UInt64 → Array UInt64 → Array UInt64 → Array UInt64
  | 0, _, _, _, _, reversed => reversed.reverse
  | count+1, i, state, terrain, history, reversed =>
    let reversed := (reversed.push (speed state)).push (altitude (floorAt terrain i) state)
    let parent := if i > 0 then history[(i-1)*stateCount+state]!.toNat else state
    unwind count (i-1) parent terrain history reversed

/-- Input: 0..64 terrain elevations in 0..1,000,000 relative to a datum.
Output: [alt0,speed0,...]. Endpoints are on the ground and at rest.
Empty input returns []; invalid input also returns [], never a partial flight.
The all-stop witness ensures the terminal stopped state is always reachable.
-/
def compute (terrain : Array UInt64) : Array UInt64 :=
  if terrain.size == 0 || terrain.size > 64 then #[]
  else if validHeights terrain.size terrain then
    let history := buildHistory (terrain.size-1) 1 terrain initial #[]
    unwind terrain.size (terrain.size-1) 0 terrain history #[]
  else #[]

end LeanExe.Examples.Drone
