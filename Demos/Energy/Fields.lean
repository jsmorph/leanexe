import Demos.Energy.Flat

/-! The authorizer over fields.  `authorizeFlat` decides as `authorizeWith` does, with the profile
table's words and the snapshot's words as the fields of the structures `Prof` and `Snap`, which
have `Flat` instances, so that a caller passes them as words and the compiled code allocates no
array and reads no table.  `authorizeFlat_eq` states that it equals `authorizeWith` of the
profile table and of the array of the snapshot's words, so that every theorem about
`authorizeWith` applies to it. -/

namespace Demos.Energy

open LeanExe.Pipeline

/-- The words of a profile table, in the order of the table. -/
structure Prof where
  version : UInt64
  floor : UInt64
  ceiling : UInt64
  chargeMax : UInt64
  dischargeMax : UInt64
  importCap : UInt64
  exportCap : UInt64
  eta : UInt64
  lossMax : UInt64
  tolerance : UInt64
  fallbackLow : UInt64
  fallbackHigh : UInt64
  tau : UInt64
  window : UInt64
  deadline : UInt64

/-- The words of the authorizer's input, in the order of the input. -/
structure Snap where
  version : UInt64
  time : UInt64
  energyLow : UInt64
  energyHigh : UInt64
  mode : UInt64
  inForceLow : UInt64
  inForceHigh : UInt64
  loadLow : UInt64
  loadHigh : UInt64
  pvLow : UInt64
  pvHigh : UInt64
  low : UInt64
  high : UInt64

instance : Flat Prof (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun p => (p.version, p.floor, p.ceiling, p.chargeMax, p.dischargeMax, p.importCap,
    p.exportCap, p.eta, p.lossMax, p.tolerance, p.fallbackLow, p.fallbackHigh, p.tau, p.window,
    p.deadline)⟩

instance : Flat Snap (UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 ×
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64) :=
  ⟨fun s => (s.version, s.time, s.energyLow, s.energyHigh, s.mode, s.inForceLow, s.inForceHigh,
    s.loadLow, s.loadHigh, s.pvLow, s.pvHigh, s.low, s.high)⟩

/-- The fields of a profile table. -/
def Prof.of (site : Array UInt64) : Prof :=
  ⟨site[0]!, site[1]!, site[2]!, site[3]!, site[4]!, site[5]!, site[6]!, site[7]!, site[8]!,
    site[9]!, site[10]!, site[11]!, site[12]!, site[13]!, site[14]!⟩

/-- The authorizer's input of a snapshot. -/
def Snap.words (s : Snap) : Array UInt64 :=
  #[s.version, s.time, s.energyLow, s.energyHigh, s.mode, s.inForceLow, s.inForceHigh, s.loadLow,
    s.loadHigh, s.pvLow, s.pvHigh, s.low, s.high]

/-- `rangeOk` over fields. -/
def rangeOkF (s : Snap) : Bool :=
  s.time < timeBound && s.energyLow ≤ energyBound && s.energyHigh ≤ energyBound &&
    s.mode ≤ 1 && powerOk s.inForceLow && powerOk s.inForceHigh &&
    s.loadLow ≤ powerBound && s.loadHigh ≤ powerBound && s.pvLow ≤ powerBound &&
    s.pvHigh ≤ powerBound && powerOk s.low && powerOk s.high

/-- `orderOk` over fields. -/
def orderOkF (s : Snap) : Bool :=
  s.energyLow ≤ s.energyHigh && s.inForceLow ≤ s.inForceHigh && s.loadLow ≤ s.loadHigh &&
    s.pvLow ≤ s.pvHigh && s.low ≤ s.high

/-- `limitOk` over fields. -/
def limitOkF (p : Prof) (s : Snap) : Bool :=
  offset - p.dischargeMax ≤ s.low && s.high ≤ offset + p.chargeMax

/-- `inForceLow` over fields. -/
def inForceLowF (p : Prof) (s : Snap) : UInt64 :=
  if s.mode == 1 then p.fallbackLow else s.inForceLow - p.tolerance

/-- `inForceHigh` over fields. -/
def inForceHighF (p : Prof) (s : Snap) : UInt64 :=
  if s.mode == 1 then p.fallbackHigh else s.inForceHigh + p.tolerance

/-- `lowB` over fields. -/
def lowBF (p : Prof) (s : Snap) : UInt64 :=
  min (min (inForceLowF p s) (s.low - p.tolerance)) p.fallbackLow

/-- `highB` over fields. -/
def highBF (p : Prof) (s : Snap) : UInt64 :=
  max (max (inForceHighF p s) (s.high + p.tolerance)) p.fallbackHigh

/-- `lowDrain` over fields. -/
def lowDrainF (p : Prof) (b : UInt64) : UInt64 :=
  ((offset - b) * p.window * million + p.eta - 1) / p.eta + p.lossMax * p.window

/-- `highGain` over fields. -/
def highGainF (p : Prof) (b : UInt64) : UInt64 := (b - offset) * p.window

/-- `exportOk` over fields. -/
def exportOkF (p : Prof) (s : Snap) (b : UInt64) : Bool :=
  s.pvHigh + offset ≤ s.loadLow + b + p.exportCap

/-- `floorOk` over fields. -/
def floorOkF (p : Prof) (s : Snap) (b : UInt64) : Bool :=
  p.floor + lowDrainF p b ≤ s.energyLow

/-- `importOk` over fields. -/
def importOkF (p : Prof) (s : Snap) (b : UInt64) : Bool :=
  s.loadHigh + b ≤ p.importCap + s.pvLow + offset

/-- `ceilingOk` over fields. -/
def ceilingOkF (p : Prof) (s : Snap) (b : UInt64) : Bool :=
  s.energyHigh + highGainF p b ≤ p.ceiling

/-- `authorizeWith` over fields: the decision for the snapshot `s` under the profile `p`. -/
def authorizeFlat (p : Prof) (s : Snap) : Decision :=
  if s.version != 1 then reject .version
  else if !rangeOkF s then reject .range
  else if !orderOkF s then reject .order
  else if !limitOkF p s then reject .power
  else
    let lo := lowBF p s
    let hi := highBF p s
    let lower : Bool := lo < p.fallbackLow
    let upper : Bool := p.fallbackHigh < hi
    if lower && !exportOkF p s lo then reject .exportCap
    else if lower && !floorOkF p s lo then reject .floor
    else if upper && !importOkF p s hi then reject .importCap
    else if upper && !ceilingOkF p s hi then reject .ceiling
    else { status := .accepted, low := s.low, high := s.high,
           expiry := s.time + p.window - p.tau }

/-! ## The equation with `authorizeWith` -/

theorem words_size (s : Snap) : (s.words.size.toUInt64 != 13) = false := rfl

theorem word_snap_0 (s : Snap) : word s.words 0 = s.version := rfl
theorem word_snap_1 (s : Snap) : word s.words 1 = s.time := rfl
theorem word_snap_2 (s : Snap) : word s.words 2 = s.energyLow := rfl
theorem word_snap_3 (s : Snap) : word s.words 3 = s.energyHigh := rfl
theorem word_snap_4 (s : Snap) : word s.words 4 = s.mode := rfl
theorem word_snap_5 (s : Snap) : word s.words 5 = s.inForceLow := rfl
theorem word_snap_6 (s : Snap) : word s.words 6 = s.inForceHigh := rfl
theorem word_snap_7 (s : Snap) : word s.words 7 = s.loadLow := rfl
theorem word_snap_8 (s : Snap) : word s.words 8 = s.loadHigh := rfl
theorem word_snap_9 (s : Snap) : word s.words 9 = s.pvLow := rfl
theorem word_snap_10 (s : Snap) : word s.words 10 = s.pvHigh := rfl
theorem word_snap_11 (s : Snap) : word s.words 11 = s.low := rfl
theorem word_snap_12 (s : Snap) : word s.words 12 = s.high := rfl

theorem word_prof_1 (site : Array UInt64) : word site 1 = (Prof.of site).floor := rfl
theorem word_prof_2 (site : Array UInt64) : word site 2 = (Prof.of site).ceiling := rfl
theorem word_prof_3 (site : Array UInt64) : word site 3 = (Prof.of site).chargeMax := rfl
theorem word_prof_4 (site : Array UInt64) : word site 4 = (Prof.of site).dischargeMax := rfl
theorem word_prof_5 (site : Array UInt64) : word site 5 = (Prof.of site).importCap := rfl
theorem word_prof_6 (site : Array UInt64) : word site 6 = (Prof.of site).exportCap := rfl
theorem word_prof_7 (site : Array UInt64) : word site 7 = (Prof.of site).eta := rfl
theorem word_prof_8 (site : Array UInt64) : word site 8 = (Prof.of site).lossMax := rfl
theorem word_prof_9 (site : Array UInt64) : word site 9 = (Prof.of site).tolerance := rfl
theorem word_prof_10 (site : Array UInt64) : word site 10 = (Prof.of site).fallbackLow := rfl
theorem word_prof_11 (site : Array UInt64) : word site 11 = (Prof.of site).fallbackHigh := rfl
theorem word_prof_12 (site : Array UInt64) : word site 12 = (Prof.of site).tau := rfl
theorem word_prof_13 (site : Array UInt64) : word site 13 = (Prof.of site).window := rfl
theorem word_prof_14 (site : Array UInt64) : word site 14 = (Prof.of site).deadline := rfl

theorem authorizeFlat_eq (site : Array UInt64) (s : Snap) :
    authorizeFlat (Prof.of site) s = authorizeWith site s.words := by
  simp only [authorizeWith, rangeOk, orderOk, limitOk, inForceLow, inForceHigh, lowB, highB,
    lowDrain, highGain, exportOk, floorOk, importOk, ceilingOk, words_size, Bool.false_eq_true,
    ite_false, word_snap_0, word_snap_1, word_snap_2, word_snap_3, word_snap_4, word_snap_5,
    word_snap_6, word_snap_7, word_snap_8, word_snap_9, word_snap_10, word_snap_11, word_snap_12]
  simp only [authorizeFlat, rangeOkF, orderOkF, limitOkF, inForceLowF, inForceHighF, lowBF,
    highBF, lowDrainF, highGainF, exportOkF, floorOkF, importOkF, ceilingOkF, word_prof_1,
    word_prof_2, word_prof_3, word_prof_4, word_prof_5, word_prof_6, word_prof_7, word_prof_8,
    word_prof_9, word_prof_10, word_prof_11, word_prof_12, word_prof_13]
  rfl

end Demos.Energy
