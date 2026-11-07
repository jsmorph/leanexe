import Demos.Energy.Fields
import Demos.Energy.Site

/-! The gateway of the energy controller, as a machine over records in the verified compiler's
dialect.  Each step, a tick, reads one input record and writes one output record.  The input
holds a sequence number, the clock, the time of the measurements, measured battery power, load,
and PV, the BMS's energy interval, the inverter's read-back of its mode and limits, and a
proposal: a flag, the load and PV intervals, and the proposed limits.  The output holds the
sequence number, the kind of output (nothing, a command, or a request to return to fallback), a
command's limits and revert timeout, and the status of the last snapshot.  The state holds the
expected sequence number, the largest clock seen, the recorded state in force with its expiry and
the time of its last change, and the window in force.

A tick applies these rules in order.  A command in force whose expiry has passed becomes fallback,
changed at its expiry.  A record with the wrong sequence number, a clock below the largest seen or
beyond the authorizer's range, or old measurements requests fallback, and so does the first
tick.  Before the end of a window in force, load or PV outside the snapshot's intervals or battery
power outside the window's interval `B` requests fallback, and so does a read-back that differs
from the recorded state at least `τ` after the last change.  A proposal becomes a snapshot only
when the read-back equals the recorded state, battery power lies in the recorded state's
interval, and the last change lies at least `τ` before the clock.  An accepted snapshot sends its
command in the same tick and becomes the window in force, and a rejected one changes only the
reported status.  A request to return to fallback records fallback, changed at the clock, and ends
the window. -/

namespace Demos.Energy

open LeanExe.Pipeline

/-- An input record. -/
structure GwIn where
  seq : UInt64
  clock : UInt64
  measured : UInt64
  power : UInt64
  load : UInt64
  pv : UInt64
  energyLow : UInt64
  energyHigh : UInt64
  readMode : UInt64
  readLow : UInt64
  readHigh : UInt64
  proposal : UInt64
  loadLow : UInt64
  loadHigh : UInt64
  pvLow : UInt64
  pvHigh : UInt64
  low : UInt64
  high : UInt64

/-- An output record.  The kind is 0 for nothing, 1 for a command, and 2 for a request to return
to fallback. -/
structure GwOut where
  seq : UInt64
  kind : UInt64
  low : UInt64
  high : UInt64
  revert : UInt64
  status : UInt64

/-- The gateway's state.  The recorded state is `mode` (0 a command, 1 fallback), its limits, a
command's expiry, and the time of its last change.  The window in force has its end, the
interval `B`, and the snapshot's load and PV intervals. -/
structure GwState where
  seq : UInt64
  clock : UInt64
  started : UInt64
  mode : UInt64
  low : UInt64
  high : UInt64
  expiry : UInt64
  changed : UInt64
  window : UInt64
  windowEnd : UInt64
  bLow : UInt64
  bHigh : UInt64
  loadLow : UInt64
  loadHigh : UInt64
  pvLow : UInt64
  pvHigh : UInt64
  status : UInt64

instance : Flat GwIn (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64) :=
  ⟨fun i => (i.seq, i.clock, i.measured, i.power, i.load, i.pv, i.energyLow, i.energyHigh,
    i.readMode, i.readLow, i.readHigh, i.proposal, i.loadLow, i.loadHigh, i.pvLow, i.pvHigh,
    i.low, i.high)⟩

instance : Flat GwOut (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun o => (o.seq, o.kind, o.low, o.high, o.revert, o.status)⟩

instance : Flat GwState (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun g => (g.seq, g.clock, g.started, g.mode, g.low, g.high, g.expiry, g.changed, g.window,
    g.windowEnd, g.bLow, g.bHigh, g.loadLow, g.loadHigh, g.pvLow, g.pvHigh, g.status)⟩

/-- The largest age of measurements that the gateway accepts, s. -/
def staleBound : UInt64 := 120

/-- The word of a status: the index of its constructor. -/
def statusWord (s : Status) : UInt64 :=
  match s with
  | .accepted => 0
  | .length => 1
  | .version => 2
  | .range => 3
  | .order => 4
  | .power => 5
  | .exportCap => 6
  | .floor => 7
  | .importCap => 8
  | .ceiling => 9

/-- The state after a request to return to fallback at time `t`. -/
def fallbackAt (g : GwState) (t : UInt64) : GwState :=
  { g with mode := 1, low := offset, high := offset, expiry := 0, changed := t, window := 0 }

/-- The state after the expiry check at the clock `c`: a command whose expiry is at most `c`
becomes fallback, changed at its expiry. -/
def expire (g : GwState) (c : UInt64) : GwState :=
  if g.mode == 0 && g.expiry ≤ c then
    { g with mode := 1, low := offset, high := offset, expiry := 0, changed := g.expiry }
  else g

/-- Whether the inverter's read-back equals the recorded state.  In fallback mode the limits are
not compared. -/
def readBackOk (g : GwState) (i : GwIn) : Bool :=
  i.readMode == g.mode && (g.mode == 1 || (i.readLow == g.low && i.readHigh == g.high))

/-- Whether battery power `w` lies in the interval of the recorded state. -/
def powerIn (p : Prof) (g : GwState) (w : UInt64) : Bool :=
  if g.mode == 1 then p.fallbackLow ≤ w && w ≤ p.fallbackHigh
  else g.low - p.tolerance ≤ w && w ≤ g.high + p.tolerance

/-- Whether the measurements at the clock `c` leave the window in force before its end. -/
def leavesWindow (g : GwState) (i : GwIn) (c : UInt64) : Bool :=
  g.window == 1 && c < g.windowEnd && (i.load < g.loadLow || g.loadHigh < i.load ||
    i.pv < g.pvLow || g.pvHigh < i.pv || i.power < g.bLow || g.bHigh < i.power)

/-- Whether the record is faulty: the first tick, a wrong sequence number, a clock below the
largest seen or beyond the authorizer's range, or old measurements. -/
def faulty (g : GwState) (i : GwIn) : Bool :=
  g.started == 0 || i.seq != g.seq || i.clock < g.clock || timeBound ≤ i.clock ||
    i.clock < i.measured || staleBound < i.clock - i.measured

/-- The clock of the tick: the record's clock, or the largest clock seen when the record's clock
lies below it or beyond the authorizer's range. -/
def tickClock (g : GwState) (i : GwIn) : UInt64 :=
  if i.clock < g.clock || timeBound ≤ i.clock then g.clock else i.clock

/-- The snapshot of the tick at the clock `c`. -/
def snapOf (g : GwState) (i : GwIn) (c : UInt64) : Snap :=
  ⟨1, c, i.energyLow, i.energyHigh, g.mode, g.low, g.high, i.loadLow, i.loadHigh, i.pvLow,
    i.pvHigh, i.low, i.high⟩

/-- One tick of the gateway under the profile `p`. -/
def gatewayWith (p : Prof) (g : GwState) (i : GwIn) : GwState × GwOut :=
  let c := tickClock g i
  let g2 := expire { g with seq := g.seq + 1, clock := c, started := 1 } c
  if faulty g i then (fallbackAt g2 c, ⟨i.seq, 2, 0, 0, 0, g.status⟩)
  else if leavesWindow g2 i c || (!readBackOk g2 i && g2.changed + p.tau ≤ c) then
    (fallbackAt g2 c, ⟨i.seq, 2, 0, 0, 0, g.status⟩)
  else if i.proposal == 1 && readBackOk g2 i && powerIn p g2 i.power &&
      g2.changed + p.tau ≤ c then
    let s := snapOf g2 i c
    let d := authorizeFlat p s
    if d.status == .accepted then
      ({ g2 with
          mode := 0, low := d.low, high := d.high, expiry := d.expiry, changed := c, window := 1,
          windowEnd := c + p.window, bLow := lowBF p s, bHigh := highBF p s, loadLow := i.loadLow, loadHigh := i.loadHigh,
          pvLow := i.pvLow, pvHigh := i.pvHigh, status := 0 },
        ⟨i.seq, 1, d.low, d.high, d.expiry - c, 0⟩)
    else ({ g2 with status := statusWord d.status }, ⟨i.seq, 0, 0, 0, 0, statusWord d.status⟩)
  else (g2, ⟨i.seq, 0, 0, 0, 0, g2.status⟩)

/-- The test site's profile as fields. -/
def siteProf : Prof :=
  ⟨1, 10800000, 34200000, 5000, 5000, 5000, 2000, 900000, 20, 50, 4294967246, 4294967346, 30,
    900, 60⟩

theorem siteProf_eq : siteProf = Prof.of site := rfl

/-- The gateway of the test site. -/
def gateway (g : GwState) (i : GwIn) : GwState × GwOut := gatewayWith siteProf g i

/-- The gateway's initial state: no tick yet, fallback recorded. -/
def gw0 : GwState := ⟨0, 0, 0, 1, offset, offset, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

end Demos.Energy
