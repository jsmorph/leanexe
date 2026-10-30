import Demos.Energy.Spec

/-! The meaning of the authorizer's words in the specification's terms.  `profileOf` and
`snapshotOf` read the profile table and the input words into the records of `Spec`, with a signed
power `p` stored as the word `p + 2 ^ 32`.  `ProfileValid` is the validity condition of a profile
table, which `site_valid` proves for the test site, and `InputValid` the condition that the
authorizer's checks before the side tests accept. -/

namespace Demos.Energy.Words

open Spec

/-- The signed power of a word that holds `p + 2 ^ 32`. -/
def signed (w : UInt64) : ℤ := (w.toNat : ℤ) - 4294967296

/-- The profile that a table holds. -/
def profileOf (site : Array UInt64) : Profile where
  floor := site[1]!.toNat
  ceiling := site[2]!.toNat
  chargeMax := site[3]!.toNat
  dischargeMax := site[4]!.toNat
  importCap := site[5]!.toNat
  exportCap := site[6]!.toNat
  eta := site[7]!.toNat
  lossMax := site[8]!.toNat
  tolerance := site[9]!.toNat
  fallbackLow := signed site[10]!
  fallbackHigh := signed site[11]!
  transition := site[12]!.toNat
  window := site[13]!.toNat
  sendDeadline := site[14]!.toNat

/-- The snapshot that input words hold. -/
def snapshotOf (xs : Array UInt64) : Snapshot where
  time := xs[1]!.toNat
  energyLow := xs[2]!.toNat
  energyHigh := xs[3]!.toNat
  state := if xs[4]! = 1 then .fallback else .command (signed xs[5]!)
  loadLow := xs[6]!.toNat
  loadHigh := xs[7]!.toNat
  pvLow := xs[8]!.toNat
  pvHigh := xs[9]!.toNat

/-- The proposed setpoint that input words hold. -/
def setpointOf (xs : Array UInt64) : ℤ := signed xs[10]!

/-- A signed power word within `2 ^ 20` of zero. -/
def PowerWord (w : UInt64) : Prop := 2 ^ 32 - 2 ^ 20 ≤ w.toNat ∧ w.toNat ≤ 2 ^ 32 + 2 ^ 20

/-- The validity condition of a profile table: the ranges that keep the authorizer's arithmetic
exact, a positive efficiency bound, a fallback interval that contains 0, and a window long enough
for the gateway's send deadline and two transitions. -/
structure ProfileValid (site : Array UInt64) : Prop where
  size : site.size = 15
  version : site[0]! = 1
  floor : site[1]!.toNat ≤ site[2]!.toNat
  ceiling : site[2]!.toNat ≤ 2 ^ 42
  charge : site[3]!.toNat ≤ 2 ^ 20
  discharge : site[4]!.toNat ≤ 2 ^ 20
  importCap : site[5]!.toNat ≤ 2 ^ 20
  exportCap : site[6]!.toNat ≤ 2 ^ 20
  etaLow : 500000 ≤ site[7]!.toNat
  etaHigh : site[7]!.toNat ≤ 1000000
  loss : site[8]!.toNat ≤ 2 ^ 20
  tolerance : site[9]!.toNat ≤ 2 ^ 20
  fallbackLow : 2 ^ 32 - 2 ^ 20 ≤ site[10]!.toNat ∧ site[10]!.toNat ≤ 2 ^ 32
  fallbackHigh : 2 ^ 32 ≤ site[11]!.toNat ∧ site[11]!.toNat ≤ 2 ^ 32 + 2 ^ 20
  window : site[13]!.toNat ≤ 3600
  timing : site[14]!.toNat + 2 * site[12]!.toNat < site[13]!.toNat

/-- The input words that the authorizer's checks before the side tests accept. -/
structure InputValid (site xs : Array UInt64) : Prop where
  size : xs.size.toUInt64 = 11
  version : xs[0]! = 1
  time : xs[1]!.toNat < 2 ^ 40
  energy : xs[2]!.toNat ≤ xs[3]!.toNat ∧ xs[3]!.toNat ≤ 2 ^ 42
  mode : xs[4]!.toNat ≤ 1
  inForce : PowerWord xs[5]!
  load : xs[6]!.toNat ≤ xs[7]!.toNat ∧ xs[7]!.toNat ≤ 2 ^ 20
  pv : xs[8]!.toNat ≤ xs[9]!.toNat ∧ xs[9]!.toNat ≤ 2 ^ 20
  setpoint : PowerWord xs[10]!
  limit : 2 ^ 32 - site[4]!.toNat ≤ xs[10]!.toNat ∧ xs[10]!.toNat ≤ 2 ^ 32 + site[3]!.toNat

end Demos.Energy.Words
