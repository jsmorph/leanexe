import Demos.Geolocation.Spec
import Demos.Frames.Program
import Demos.Screening.Program

/-!
The geolocation program.  `locateWith` reads an array of binary64 values, encloses the receivers'
Earth-fixed states (`receivers`), searches the region by interval branch-and-prune level by level
(`search`), tests the boxes left untested (`finalBoxes`), and writes the boxes with their labels.
`requirements.md` states the interface, and `Soundness.lean` proves what the boxes imply.
-/

namespace Demos.Geolocation

open Library.Numerics.Bounds Library.Numerics.Interval Library.Numerics.Float64
open Demos.Screening (rd middle allFinite isWhole)

/-- A box of latitudes, longitudes, and heights, with its mark: 0 untested, 1 undecided, and 2
when every point of it fits the measurements. -/
structure Box where
  plo : Float
  phi : Float
  llo : Float
  lhi : Float
  hlo : Float
  hhi : Float
  mark : UInt64
  deriving Inhabited

/-- The state of the measurements' loop in a box test: some measurement excludes the box, and
every measurement so far holds over it. -/
structure Verdict where
  out : Bool
  inner : Bool
  deriving Inhabited

/-- The state of the search: the boxes, the status, 2 while it refines, 0 once no box is left
untested, and 1 once it stops at the cap, the number of box tests, and the number of levels
completed. -/
structure Search where
  boxes : Array Box
  status : UInt64
  tests : UInt64
  levels : UInt64
  deriving Inhabited

/-- The Earth-fixed state of a receiver: its position and its velocity. -/
structure State where
  x : Interval
  y : Interval
  z : Interval
  u : Interval
  v : Interval
  w : Interval
  deriving Inhabited

/-! ### Receivers -/

/-- The interval of the input values at `q` and `q + 1`. -/
def pair (xs : Array Float) (q : UInt64) : Interval := make (rd xs q) (rd xs (q + 1))

/-- The Earth-fixed state of the receiver whose entries start at `b`. -/
def stateOf (xs : Array Float) (b : UInt64) : State :=
  ⟨pair xs (b + 2), pair xs (b + 4), pair xs (b + 6), pair xs (b + 8), pair xs (b + 10),
    pair xs (b + 12)⟩

/-- Component `c` of a state, in the order of its fields. -/
def component (s : State) (c : UInt64) : Interval :=
  if c == 0 then s.x else if c == 1 then s.y else if c == 2 then s.z
  else if c == 3 then s.u else if c == 4 then s.v else s.w

/-- The intervals of the `n` receivers' states, six for each receiver in the order of `State`. -/
def receivers (xs : Array Float) (n : UInt64) : Array Interval :=
  LeanExe.build (6 * n) fun q => component (stateOf xs (20 + 14 * (q / 6))) (q % 6)

/-- Every interval is accepted. -/
def allAccepted (ys : Array Interval) : Bool :=
  LeanExe.loop ys.size.toUInt64 true fun i ok => ok && ys[i.toNat]!.status == 0

/-! ### The box test -/

/-- The interval of the residual of the measurement whose entries start at `q`, over the
Earth-fixed box `(px, py, pz)`. -/
def residual (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (q : UInt64) (px py pz : Interval) : Interval :=
  let i := 6 * (rd xs (q + 1)).toUInt64
  let j := 6 * (rd xs (q + 2)).toUInt64
  let v := point (rd xs (q + 3))
  if rd xs q == 1.0 then
    tdoaResI inv half inv half rx[i.toNat]! rx[(i + 1).toNat]! rx[(i + 2).toNat]! rx[j.toNat]!
      rx[(j + 1).toNat]! rx[(j + 2).toNat]! px py pz v
  else
    fdoaResI inv half inv half fq rx[i.toNat]! rx[(i + 1).toNat]! rx[(i + 2).toNat]!
      rx[(i + 3).toNat]! rx[(i + 4).toNat]! rx[(i + 5).toNat]! rx[j.toNat]! rx[(j + 1).toNat]!
      rx[(j + 2).toNat]! rx[(j + 3).toNat]! rx[(j + 4).toNat]! rx[(j + 5).toNat]! px py pz v

/-- One measurement's step of the box test. -/
def verdictStep (inv half : Array UInt64) (rx : Array Interval) (fq : Interval)
    (xs : Array Float) (base : UInt64) (px py pz : Interval) (k : UInt64) (v : Verdict) :
    Verdict :=
  if v.out then v
  else
    let q := base + 5 * k
    let e := residual inv half rx fq xs q px py pz
    let eps := rd xs (q + 4)
    if e.status == 0 then
      if eps < e.lo || e.hi < -eps then ⟨true, false⟩
      else ⟨false, v.inner && -eps ≤ e.lo && e.hi ≤ eps⟩
    else ⟨false, false⟩

/-- The test of a box against the `m` measurements whose entries start at `base`: 0 when some
measurement excludes it, 2 when every measurement holds over it, and 1 otherwise. -/
def boxTest (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (b : Box) : UInt64 :=
  let p := Demos.Frames.cartesianI inv half inv half (make b.plo b.phi) (make b.llo b.lhi)
    (make b.hlo b.hhi)
  let v := LeanExe.loop m (⟨false, true⟩ : Verdict) fun k v =>
    verdictStep inv half rx fq xs base p.1 p.2.1 p.2.2 k v
  if v.out then 0 else if v.inner then 2 else 1

/-! ### Splitting -/

/-- The longest side of a box, 0 for the latitude, 1 for the longitude, and 2 for the height, and
its size in km. -/
def longest (b : Box) : UInt64 × Float :=
  let sa := 6378.137 * (b.phi - b.plo)
  let sb := 6378.137 * (b.lhi - b.llo)
  let sc := b.hhi - b.hlo
  if sb ≤ sa && sc ≤ sa then (0, sa) else if sc ≤ sb then (1, sb) else (2, sc)

def sideLo (b : Box) (side : UInt64) : Float :=
  if side == 0 then b.plo else if side == 1 then b.llo else b.hlo

def sideHi (b : Box) (side : UInt64) : Float :=
  if side == 0 then b.phi else if side == 1 then b.lhi else b.hhi

/-- The half of a box below `m` on a side, untested. -/
def lowerHalf (b : Box) (side : UInt64) (m : Float) : Box :=
  if side == 0 then { b with phi := m, mark := 0 }
  else if side == 1 then { b with lhi := m, mark := 0 }
  else { b with hhi := m, mark := 0 }

/-- The half of a box above `m` on a side, untested. -/
def upperHalf (b : Box) (side : UInt64) (m : Float) : Box :=
  if side == 0 then { b with plo := m, mark := 0 }
  else if side == 1 then { b with llo := m, mark := 0 }
  else { b with hlo := m, mark := 0 }

/-- The box is larger than the resolution `r`, and the middle of its longest side lies strictly
between the side's ends. -/
def splits (r : Float) (b : Box) : Bool :=
  let s := longest b
  let md := middle (sideLo b s.1) (sideHi b s.1)
  r < s.2 && finite md && sideLo b s.1 < md && md < sideHi b s.1

/-! ### The search -/

/-- One box's step of a level: a tested box is kept, and an untested box is dropped, kept with
mark 2, split at the middle of its longest side, or kept with mark 1. -/
def boxStep (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (r : Float) (b : Box) (acc : Array Box) : Array Box :=
  if b.mark == 0 then
    let t := boxTest inv half rx fq xs base m b
    if t == 0 then acc
    else if t == 2 then acc.push { b with mark := 2 }
    else if splits r b then
      let side := (longest b).1
      let md := middle (sideLo b side) (sideHi b side)
      (acc.push (lowerHalf b side md)).push (upperHalf b side md)
    else acc.push { b with mark := 1 }
  else acc.push b

/-- The boxes of the next level. -/
def refine (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (r : Float) (boxes : Array Box) : Array Box :=
  LeanExe.loop boxes.size.toUInt64 #[] fun i acc =>
    boxStep inv half rx fq xs base m r boxes[i.toNat]! acc

/-- The number of untested boxes. -/
def fresh (boxes : Array Box) : UInt64 :=
  LeanExe.loop boxes.size.toUInt64 0 fun i k => if boxes[i.toNat]!.mark == 0 then k + 1 else k

/-- One level of the search: refine, or stop at the cap with the boxes of the level. -/
def level (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (r : Float) (cap : UInt64) (s : Search) : Search :=
  if s.status == 2 then
    let next := refine inv half rx fq xs base m r s.boxes
    let tests := s.tests + fresh s.boxes
    if cap < next.size.toUInt64 then ⟨s.boxes, 1, tests, s.levels⟩
    else if fresh next == 0 then ⟨next, 0, tests, s.levels + 1⟩
    else ⟨next, 2, tests, s.levels + 1⟩
  else s

/-- The search from the region `b`, with at most `levels` levels and `cap` boxes. -/
def search (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (r : Float) (b : Box) (levels cap : UInt64) : Search :=
  LeanExe.loop levels ⟨(#[] : Array Box).push b, 2, 0, 0⟩ fun _ s =>
    level inv half rx fq xs base m r cap s

/-- One box's step of the final pass: an untested box is tested, and dropped or kept with its
test's result as its mark. -/
def finalStep (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (b : Box) (acc : Array Box) : Array Box :=
  if b.mark == 0 then
    let t := boxTest inv half rx fq xs base m b
    if t == 0 then acc else acc.push { b with mark := t }
  else acc.push b

/-- The boxes that the final pass keeps. -/
def finalBoxes (inv half : Array UInt64) (rx : Array Interval) (fq : Interval) (xs : Array Float)
    (base m : UInt64) (boxes : Array Box) : Array Box :=
  LeanExe.loop boxes.size.toUInt64 #[] fun i acc =>
    finalStep inv half rx fq xs base m boxes[i.toNat]! acc

/-! ### Input and output -/

/-- The input values at `q` and `q + 1` are ordered. -/
def ordered (xs : Array Float) (q : UInt64) : Bool := rd xs q ≤ rd xs (q + 1)

/-- The seven intervals of the receiver whose entries start at `b` are ordered. -/
def receiverOk (xs : Array Float) (b : UInt64) : Bool :=
  ordered xs b && ordered xs (b + 2) && ordered xs (b + 4) && ordered xs (b + 6) &&
    ordered xs (b + 8) && ordered xs (b + 10) && ordered xs (b + 12)

/-- The measurement whose entries start at `q` meets its requirements for `n` receivers. -/
def measurementOk (xs : Array Float) (n q : UInt64) : Bool :=
  (rd xs q == 1.0 || rd xs q == 2.0) && isWhole (rd xs (q + 1)) 0 (n - 1) &&
    isWhole (rd xs (q + 2)) 0 (n - 1) && rd xs (q + 1) != rd xs (q + 2) && 0.0 ≤ rd xs (q + 4)

/-- Every receiver and every measurement meets its requirements. -/
def entriesOk (xs : Array Float) (n m : UInt64) : Bool :=
  let a := LeanExe.loop n true fun i ok => ok && receiverOk xs (20 + 14 * i)
  let b := LeanExe.loop m true fun k ok => ok && measurementOk xs n (20 + 14 * n + 5 * k)
  a && b

/-- The input meets the requirements of `requirements.md`. -/
def valid (xs : Array Float) : Bool :=
  20 ≤ xs.size.toUInt64 && allFinite xs && rd xs 0 == 1.0 && rd xs 1 == 0.0 &&
    isWhole (rd xs 2) 2 16 && isWhole (rd xs 3) 1 64 &&
    xs.size.toUInt64 == 20 + 14 * (rd xs 2).toUInt64 + 5 * (rd xs 3).toUInt64 &&
    isWhole (rd xs 4) 0 4294967295 && ordered xs 5 && ordered xs 7 && 0.0 < rd xs 9 &&
    ordered xs 9 && ordered xs 11 && ordered xs 13 && ordered xs 15 && 0.0 < rd xs 17 &&
    isWhole (rd xs 18) 0 128 && isWhole (rd xs 19) 1 65536 &&
    entriesOk xs (rd xs 2).toUInt64 (rd xs 3).toUInt64

/-- The boxes as seven values each: the ends of the latitude, the longitude, and the height, and
the label, 1 for mark 2 and 0 otherwise. -/
def sevens (bs : Array Box) : Array Float :=
  LeanExe.build (7 * bs.size.toUInt64) fun i =>
    let b := bs[(i / 7).toNat]!
    let k := i % 7
    if k == 0 then b.plo else if k == 1 then b.phi else if k == 2 then b.llo
    else if k == 3 then b.lhi else if k == 4 then b.hlo else if k == 5 then b.hhi
    else if b.mark == 2 then 1.0 else 0.0

/-- The output of a search and its final boxes. -/
def outputOf (s : Search) (bs : Array Box) : Array Float :=
  #[s.status.toFloat, bs.size.toUInt64.toFloat, (s.tests + fresh s.boxes).toFloat,
    s.levels.toFloat] ++ sevens bs

/-- The region of the input as one untested box. -/
def regionOf (xs : Array Float) : Box :=
  ⟨rd xs 11, rd xs 12, rd xs 13, rd xs 14, rd xs 15, rd xs 16, 0⟩

/-- The boxes that hold every emitter position consistent with the measurements of `xs`. -/
def locateWith (inv half : Array UInt64) (xs : Array Float) : Array Float :=
  if valid xs then
    let n := (rd xs 2).toUInt64
    let m := (rd xs 3).toUInt64
    let rx := receivers xs n
    if allAccepted rx then
      let fq := pair xs 9
      let base := 20 + 14 * n
      let s := search inv half rx fq xs base m (rd xs 17) (regionOf xs) (rd xs 18).toUInt64
        (rd xs 19).toUInt64
      outputOf s (finalBoxes inv half rx fq xs base m s.boxes)
    else #[4.0, 0.0, 0.0, 0.0]
  else #[3.0, 0.0, 0.0, 0.0]

def locate (xs : Array Float) : Array Float :=
  locateWith Library.Numerics.Float64.Trig.invPi Library.Numerics.Float64.Trig.halfPi xs

end Demos.Geolocation
