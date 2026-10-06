import LeanExe.Dialect.Build
import LeanExe.Dialect.Loop
import LeanExe.Dialect.RepeatWhile

/-!
An ideal point-mass autopilot with an exact shortest-path search over a finite graph of motion
primitives, rewritten from the earlier system's `Examples/Drone/Program.lean` in this dialect.  A
flight passes up to 64 stations with terrain heights from 0 to 1,000,000.  At each station the drone
is in one of 45 states: 9 altitudes 25 apart above the station's floor, and 5 horizontal speeds from
0 to 20.  An edge between states at adjacent stations is admitted when its segment keeps the speed,
acceleration, and clearance limits, and it costs its duration in ticks of 1/840 second, with the
altitude above the floor as the second criterion.

The words are `UInt64` throughout, and the earlier system's recursions on fuel are counted loops.
The square root takes 17 halvings.  A row is a build over the 45 targets, each a loop over the 45
sources that replaces its incumbent only on strict improvement, so ties go to the lowest source.
The forward pass carries one table of all rows, and the output follows the parents back from the
last station.  Invalid input runs the same code with no stations, which returns `#[]`.
-/

namespace Examples.Drone

abbrev stateCount : UInt64 := 45
abbrev infinity : UInt64 := 1000000000000

def distance (a b : UInt64) : UInt64 := if a ≥ b then a - b else b - a

def altitude (floor state : UInt64) : UInt64 := floor + state / 5 * 25

def speed (state : UInt64) : UInt64 := state % 5 * 5

/-- The clearance floor of station `i`: the terrain height, plus 100 between the endpoints. -/
@[inline] def floorAt (terrain : Array UInt64) (i : UInt64) : UInt64 :=
  let size := terrain.size.toUInt64
  terrain[i.toNat]! + if i == 0 || i + 1 == size then 0 else 100

/-- The least `r` with `n ≤ r * r`, for `n ≤ 2^32`, by 17 halvings of the bracket
`[0, 65536]`. -/
def ceilSqrt (n : UInt64) : UInt64 :=
  match LeanExe.loop 17 ((0 : UInt64), (65536 : UInt64)) fun _ bracket =>
      let mid := (bracket.1 + bracket.2) / 2
      (if bracket.1 < bracket.2 && mid * mid < n then mid + 1 else bracket.1,
        if bracket.1 < bracket.2 && n ≤ mid * mid then mid else bracket.2) with
  | (lo, _) => lo

/-- The least whole number of seconds for a rest-to-rest segment with height change `dh`
that keeps the horizontal and vertical speed and acceleration limits. -/
def restSeconds (dh : UInt64) : UInt64 :=
  let root := ceilSqrt ((3 * dh + 1) / 2)
  max 25 (max ((3 * dh + 39) / 40) root)

/-- The ticks of the segment from altitude `z0` over floor `r0` at speed `u` to altitude `z1`
over floor `r1` at speed `v`, or 0 when a limit rejects it. -/
def edgeTicks (r0 r1 z0 z1 u v : UInt64) : UInt64 :=
  let dh := distance z0 z1
  let skew := distance (u * u) (v * v)
  let rest := restSeconds dh
  let total := u + v
  let moving := 33600 / (total / 5)
  if total == 0 then 840 * rest
  else if 200 < skew || 8000 < 3 * dh * total || 160000 < 6 * dh * total * total ||
      (r0 ≤ r1 && 3 * total * (z0 - r0) < 2 * u * (r1 - r0)) ||
      (r1 < r0 && 3 * total * (z1 - r1) < 2 * v * (r0 - r1)) then 0
  else moving

/-- The best known flight to a state: its ticks, its altitude above the floors, and the state
at the previous station. -/
structure Choice where
  time : UInt64
  excess : UInt64
  parent : UInt64
  deriving Inhabited, DecidableEq, Repr

abbrev unreachable : Choice := ⟨infinity, infinity, 0⟩

/-- The candidate when it is strictly better, and the incumbent otherwise. -/
def choose (incumbent candidate : Choice) : Choice :=
  if candidate.time < incumbent.time ||
      (candidate.time == incumbent.time && candidate.excess < incumbent.excess)
  then candidate else incumbent

/-- The flight to `target` through `source`, whose best flight is `old`. -/
def predecessor (r0 r1 : UInt64) (old : Choice) (target source : UInt64) : Choice :=
  let z0 := altitude r0 source
  let z1 := altitude r1 target
  let u := speed source
  let v := speed target
  let dt := edgeTicks r0 r1 z0 z1 u v
  if old.time < infinity && 0 < dt then ⟨old.time + dt, old.excess + (z1 - r1), source⟩
  else unreachable

/-- The best flight to `target` through the first `sources` states of the row at `base` in
`table`, the lowest source among equals. -/
@[inline] def best (r0 r1 : UInt64) (table : Array Choice) (base target sources : UInt64) :
    Choice :=
  match LeanExe.loop sources (infinity, infinity, (0 : UInt64)) fun source acc =>
      let old := table[(base + source).toNat]!
      let candidate := predecessor r0 r1 old target source
      let c := choose ⟨acc.1, acc.2.1, acc.2.2⟩ candidate
      (c.time, c.excess, c.parent) with
  | (time, excess, parent) => ⟨time, excess, parent⟩

/-- The row of the station after the row at `base` in `table`.  The last station admits only
state 0, at rest on the ground. -/
def advance (r0 r1 : UInt64) (last : Bool) (table : Array Choice) (base : UInt64) :
    Array Choice :=
  LeanExe.build stateCount fun target =>
    best r0 r1 table base target (if !last || target == 0 then stateCount else 0)

/-- The row of the first station: state 0 at no cost, the others unreachable. -/
def initial : Array Choice :=
  LeanExe.build stateCount fun state =>
    ⟨if state == 0 then 0 else infinity, if state == 0 then 0 else infinity, 0⟩

def validHeights (terrain : Array UInt64) : Bool :=
  LeanExe.loop terrain.size.toUInt64 true fun i ok => ok && terrain[i.toNat]! ≤ 1000000

/-- Status 0 and the table extended by the row of station `i`, whose previous row ends the
table, or status 1 and the table when station `i` is past the last. -/
def extend (terrain : Array UInt64) (count i : UInt64) (table : Array Choice) :
    UInt64 × UInt64 × Array Choice :=
  let size := table.size.toUInt64
  if i < count then
    (0, i + 1, LeanExe.build (size + stateCount) fun j =>
      let target := j - size
      let r0 := floorAt terrain (i - 1)
      let r1 := floorAt terrain i
      let c := best r0 r1 table (size - stateCount) target
        (if j < size || (i + 1 == count && target != 0) then 0 else stateCount)
      ⟨if j < size then table[j.toNat]!.time else c.time,
        if j < size then table[j.toNat]!.excess else c.excess,
        if j < size then table[j.toNat]!.parent else c.parent⟩)
  else (1, i, table)

/-- The rows of the first `count` stations. -/
def forward (terrain : Array UInt64) (count : UInt64) : UInt64 × UInt64 × Array Choice :=
  LeanExe.repeatWhile 64 ((0 : UInt64), (1 : UInt64), initial) (fun (status, _, _) => status == 0)
    (fun (_, i, table) => extend terrain count i table)

/-- The altitude and speed of each station on the flight that ends at rest at the last
station, found by following the parents back. -/
def output (terrain : Array UInt64) (table : Array Choice) (count : UInt64) : Array UInt64 :=
  LeanExe.build (2 * count) fun e =>
    let k := e / 2
    let state := LeanExe.loop (count - 1 - k) (0 : UInt64) fun j s =>
      table[((count - 1 - j) * stateCount + s).toNat]!.parent
    let z := altitude (floorAt terrain k) state
    let v := speed state
    if e % 2 == 0 then z else v

/-- Input: up to 64 terrain heights, each at most 1,000,000.  Output: `[alt0, speed0, alt1,
speed1, …]`, starting and ending on the ground at rest; `#[]` for empty or invalid input. -/
def compute (terrain : Array UInt64) : Array UInt64 :=
  let n := terrain.size.toUInt64
  let valid := validHeights terrain
  let count := if 0 < n && n ≤ 64 && valid then n else 0
  match forward terrain count with
  | (_, _, table) => output terrain table count

end Examples.Drone
