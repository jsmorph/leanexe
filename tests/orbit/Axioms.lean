import Demos.Orbit.Newton
import Demos.Orbit.GibbsSound
import Demos.Orbit.GibbsVerified
import Demos.Orbit.LambertSound
import Demos.Orbit.LambertVerified
import Demos.Orbit.LambertOrbit
import Demos.Orbit.LambertTransfer

/-! The axioms of the theorems of the orbit-determination demo, which must be `propext`,
`Classical.choice`, and `Quot.sound`. -/

#print axioms Demos.Orbit.orbitOf_spec
#print axioms Demos.Orbit.gibbs_velocity
#print axioms Demos.Orbit.newton_conserves
#print axioms Demos.Orbit.gibbs_newton
#print axioms Demos.Orbit.gibbsCoords.encloses
#print axioms Demos.Orbit.gibbsBox_sound
#print axioms Demos.Orbit.gibbsBox_no_orbit
#print axioms Demos.Orbit.gibbsBounds_sound
#print axioms Demos.Orbit.gibbsCompiled.bytes
#print axioms Demos.Orbit.gibbsCompiled.gibbsBox.implements
#print axioms Demos.Orbit.gibbsCompiled.gibbsBounds.implements
#print axioms Demos.Orbit.Lambert.tof_pos_eq
#print axioms Demos.Orbit.Lambert.tof_neg_eq
#print axioms Demos.Orbit.Lambert.tof_strictAntiOn
#print axioms Demos.Orbit.Lambert.tof_continuousOn
#print axioms Demos.Orbit.Lambert.exists_unique_root
#print axioms Demos.Orbit.tofI_encloses
#print axioms Demos.Orbit.bracket_spec
#print axioms Demos.Orbit.lambertBox_sound
#print axioms Demos.Orbit.lambertBounds_sound
#print axioms Demos.Orbit.lambertCompiled.bytes
#print axioms Demos.Orbit.lambertCompiled.lambertBox.implements
#print axioms Demos.Orbit.lambertCompiled.lambertBounds.implements
#print axioms Demos.Orbit.LambertOrbit.core_one
#print axioms Demos.Orbit.LambertOrbit.core_two
#print axioms Demos.Orbit.izzo_orbit
#print axioms Demos.Orbit.izzo_energy
#print axioms Demos.Orbit.orbit_izzo
#print axioms Demos.Orbit.kepler_radius
#print axioms Demos.Orbit.keplerPos_onPath
#print axioms Demos.Orbit.keplerPos_inj
#print axioms Demos.Orbit.keplerTime_strictMono
#print axioms Demos.Orbit.kepler_newton
#print axioms Demos.Orbit.izzo_kepler
#print axioms Demos.Orbit.lambert_time
#print axioms Demos.Orbit.lambert_elliptic
#print axioms Demos.Orbit.lambert_newton
#print axioms Demos.Orbit.lambertBox_accepts
#print axioms Demos.Orbit.lambertBox_transfer
#print axioms Demos.Orbit.lambertBounds_transfer
