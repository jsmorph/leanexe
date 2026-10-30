import Verified.Reflect.Command
import Demos.Energy.Flat
import Demos.Energy.Site

/-! The energy authorizer of `Demos/Energy/Program.lean`, compiled by the verified compiler with
the test site's profile table.  `authorize` is a wrapper that passes the table `site` to
`authorizeWith`. -/

namespace Demos.Energy.Verified

open _root_.Demos.Energy

verified_compile compiled := [rangeOk, orderOk, limitOk, inForceLow, inForceHigh, lowB, highB,
  lowGain, lowDrain, highGain, highDrain, exportOk, floorOk, importOk, ceilingOk, reject,
  authorizeWith, authorize]

end Demos.Energy.Verified
