import Library.Hashing.Sha2.Equiv.SHA256.Main
import Library.Hashing.Sha2.Equiv.SHA512.Main

/-! # Axiom regression gate

Pins the axiom set the public correctness theorems depend on.  If the
build fails here, a new axiom has been introduced — review the change
deliberately and update the pinned messages below. -/

/-- info: 'SHS.Equiv.SHA256.sha256_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.sha256_correct

/-- info: 'SHS.Equiv.SHA256.compress_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.compress_correct

/-- info: 'SHS.Equiv.SHA256.sha224_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA256.sha224_correct

/-- info: 'SHS.Equiv.SHA512.sha512_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA512.sha512_correct

/-- info: 'SHS.Equiv.SHA512.compress_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA512.compress_correct

/-- info: 'SHS.Equiv.SHA512.sha384_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA512.sha384_correct

/-- info: 'SHS.Equiv.SHA512.sha512_256_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA512.sha512_256_correct

/-- info: 'SHS.Equiv.SHA512.sha512_224_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms SHS.Equiv.SHA512.sha512_224_correct
