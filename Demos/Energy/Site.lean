import Demos.Energy.Program

/-! The profile table of the test site, which is the profile of the plan's worked example: an
energy floor of 10,800,000 J and a ceiling of 34,200,000 J, a largest charge and discharge of
5,000 W, an import cap of 5,000 W, an export cap of 2,000 W, an efficiency bound of 900,000 ppm, a
largest loss rate of 20 W, a tolerance of 50 W, the fallback interval `[-50, 50]` W, a transition
time of 30 s, a window of 900 s, and a send deadline of 60 s.  `authorize` is the authorizer
under this table. -/

namespace Demos.Energy

def site : Array UInt64 :=
  #[1, 10800000, 34200000, 5000, 5000, 5000, 2000, 900000, 20, 50, 4294967246, 4294967346, 30,
    900, 60]

def authorize (xs : Array UInt64) : Decision := authorizeWith site xs

end Demos.Energy
