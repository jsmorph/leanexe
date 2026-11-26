module

public import Verified.Reflect.Command
public import Demos.Energy.Flat
public import Demos.Energy.Site
public meta import Demos.Energy.Site

@[expose] public section

/-! The energy authorizer of `Demos/Energy/Program.lean`, compiled by the verified compiler with
the test site's profile table.  `authorize` is a wrapper that passes the table `site` to
`authorizeWith`. -/

namespace Demos.Energy.Verified

open _root_.Demos.Energy

verified_compile compiled := [rangeOk, orderOk, limitOk, inForceLow, inForceHigh, lowB, highB,
  lowDrain, highGain, exportOk, floorOk, importOk, ceilingOk, reject,
  authorizeWith, authorize]

end Demos.Energy.Verified
