import Demos.Geolocation.Soundness
import Demos.Geolocation.Call

/-! The axioms of the geolocation program's theorems, which must be `propext`,
`Classical.choice`, and `Quot.sound`. -/

#print axioms Demos.Geolocation.Model.range_hasDerivAt
#print axioms Demos.Geolocation.dist.encloses
#print axioms Demos.Geolocation.rate.encloses
#print axioms Demos.Geolocation.tdoaRes.encloses
#print axioms Demos.Geolocation.fdoaRes.encloses
#print axioms Demos.Geolocation.tdoaRes_eq
#print axioms Demos.Geolocation.fdoaRes_eq
#print axioms Demos.Geolocation.halves
#print axioms Demos.Geolocation.level_inv
#print axioms Demos.Geolocation.search_inv
#print axioms Demos.Geolocation.search_status
#print axioms Demos.Geolocation.fresh_zero
#print axioms Demos.Geolocation.finalBoxes_spec
#print axioms Demos.Geolocation.receivers_sound
#print axioms Demos.Geolocation.residual_encloses
#print axioms Demos.Geolocation.verdict_spec
#print axioms Demos.Geolocation.boxTest_spec
#print axioms Demos.Geolocation.locate_cover
#print axioms Demos.Geolocation.locate_inner
#print axioms Demos.Geolocation.locate_within
#print axioms Demos.Geolocation.locate_status
#print axioms Demos.Geolocation.locate_invalid
#print axioms Demos.Geolocation.compiled.bytes
#print axioms Demos.Geolocation.compiled.locate.implements
#print axioms Demos.Geolocation.locate_call
