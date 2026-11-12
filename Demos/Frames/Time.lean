import Library.Numerics.Interval.Functions
import LeanExe.Dialect.Loop

/-!
TAI, TT, and UT1 from UTC with a leap-second table, as `requirements.md` states.  `timeScales`
checks the table `E, d₀, Δ₀, d₁, Δ₁, …` in one pass, which also finds TAI − UTC on the day `d` and
on the day `d + 1`, tests the date and the seconds against the table and the length of the day,
and returns TAI − UTC with the seconds of the day in TAI, TT, and UT1.  `TimeSound.lean` states
what each status implies.
-/

namespace Demos.Frames

open Library.Numerics.Bounds Library.Numerics.Interval

/-- A status, TAI − UTC in seconds, and the seconds of the day in TAI, TT, and UT1. -/
structure Times where
  status : UInt64
  dat : UInt64
  tai : Interval
  tt : Interval
  ut1 : Interval
  deriving Inhabited

/-- A status without values. -/
def noTimes (status : UInt64) : Times := ⟨status, 0, rejected, rejected, rejected⟩

/-- The state of the pass over a table: a status of 0 while the entries read so far are valid,
the last date read, and the offsets of the last entries whose dates are at most `d` and at most
`d + 1`. -/
structure Scan where
  status : UInt64
  last : UInt64
  dat0 : UInt64
  dat1 : UInt64
  deriving Inhabited

/-- Entry `i` of the table `xs` for the day `d`: its date and offset must lie below `2³²` and its
date above the last one. -/
def scanStep (xs : Array UInt64) (d i : UInt64) (s : Scan) : Scan :=
  let date := xs[(2 * i + 1).toNat]!
  let off := xs[(2 * i + 2).toNat]!
  if s.status == 0 then
    if date < 4294967296 && off < 4294967296 && (i == 0 || s.last < date) then
      ⟨0, date, if date ≤ d then off else s.dat0, if date ≤ d + 1 then off else s.dat1⟩
    else ⟨1, s.last, s.dat0, s.dat1⟩
  else s

/-- TAI − UTC and the seconds of day `d` in TAI, TT, and UT1 for the UTC seconds `s`, with the
leap-second table `xs` and the interval `[dlo, dhi]` of UT1 − UTC. -/
def timeScales (xs : Array UInt64) (d : UInt64) (s dlo dhi : Float) : Times :=
  let n := xs.size.toUInt64
  let e := xs[(0 : UInt64).toNat]!
  if 3 ≤ n && n % 2 == 1 && e < 4294967296 then
    let sc := LeanExe.loop ((n - 1) / 2) ⟨0, 0, 0, 0⟩ (scanStep xs d)
    if sc.status == 0 && sc.last < e then
      if xs[(1 : UInt64).toNat]! ≤ d && d < e - 1 then
        let len := 86400 + sc.dat1.toInt64 - sc.dat0.toInt64
        let u := make dlo dhi
        if finite s && 0 ≤ s && s < len.toFloat && u.status == 0 then
          let ss := point s
          let tai := add ss (ofInt sc.dat0.toInt64)
          let tt := add tai (ratio 32184 1000)
          let ut1 := add ss u
          if tai.status == 0 && tt.status == 0 && ut1.status == 0 then ⟨0, sc.dat0, tai, tt, ut1⟩
          else noTimes 4
        else noTimes 3
      else noTimes 2
    else noTimes 1
  else noTimes 1

end Demos.Frames
