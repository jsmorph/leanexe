import Demos.Sgp4.BoxVerified
import Demos.Sgp4.BoxMaster
import Demos.Sgp4.TleSound
import Demos.Sgp4.Latitude
import Demos.Sgp4.TwoBody

/-! The axioms of the theorems of the SGP4 model and of the enclosing program, which must be
`propext`, `Classical.choice`, and `Quot.sound`. -/

#print axioms Demos.Sgp4.Kepler.exists_unique_root
#print axioms Demos.Sgp4.Kepler.root_bound
#print axioms Demos.Sgp4.Kepler.root.encloses
#print axioms Demos.Sgp4.Spec.wgs72.encloses
#print axioms Demos.Sgp4.Spec.wgs72State.encloses
#print axioms Demos.Sgp4.anomaly_unit
#print axioms Demos.Sgp4.sin_latitude
#print axioms Demos.Sgp4.cos_latitude
#print axioms Demos.Sgp4.two_body
#print axioms Demos.Sgp4.sgp4Box_sound
#print axioms Demos.Sgp4.status_sound
#print axioms Demos.Sgp4.Tle.read_status
#print axioms Demos.Sgp4.Tle.read_encloses
#print axioms Demos.Sgp4.Tle.propagate_sound
#print axioms Demos.Sgp4.Tle.propagate_status
#print axioms Demos.Sgp4.sgp4Box_master
#print axioms Demos.Sgp4.sgp4BoxAround_master
#print axioms Demos.Sgp4.propagate_master
#print axioms Demos.Sgp4.boxCompiled.bytes
#print axioms Demos.Sgp4.boxCompiled.sgp4Box.implements
#print axioms Demos.Sgp4.boxCompiled.sgp4BoxAround.implements
#print axioms Demos.Sgp4.boxCompiled.propagate.implements
