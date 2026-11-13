import Demos.Conjunction.Soundness
import Demos.Conjunction.Projection
import Demos.Conjunction.MessageSoundness
import Demos.Conjunction.Verified

/-! The axioms of the conjunction program's theorems, which must be `propext`,
`Classical.choice`, and `Quot.sound`. -/

#print axioms Demos.Conjunction.Model.pc_eq
#print axioms Demos.Conjunction.Model.pc_nonneg
#print axioms Demos.Conjunction.pcWith_enclosure
#print axioms Demos.Conjunction.pcTail_sound
#print axioms Demos.Conjunction.pc_enclosure
#print axioms Demos.Conjunction.assess_sound
#print axioms Demos.Conjunction.projection_sound
#print axioms Demos.Conjunction.pcMessage_enclosure
#print axioms Demos.Conjunction.assessMessage_sound
#print axioms Demos.Conjunction.compiled.bytes
#print axioms Demos.Conjunction.compiled.pc.implements
#print axioms Demos.Conjunction.compiled.assess.implements
#print axioms Demos.Conjunction.compiled.pcMessage.implements
#print axioms Demos.Conjunction.compiled.assessMessage.implements
