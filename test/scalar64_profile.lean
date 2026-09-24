import LeanExe.Correct.Scalar64.Arithmetic

open LeanExe.TypeSafety LeanExe.Correct.Scalar64

-- Ordinary scalar typing admits unused parameters and strict unused lets.
example : checkProgram [.word .w64 7] [binarySignature] = true := by decide
example : checkProgram [.letE (.word .w64 7) (.word .w64 9)] [binarySignature] = true := by decide

-- Scalar-looking values do not admit Nat, other widths, heap values, or casts.
example : checkProgram [.nat 7] [binarySignature] = false := by decide
example : checkShape (.word .w32 7) = false := by decide
example : checkShape (.arrayEmpty (.word .w64)) = false := by decide
example : checkShape (.wordToNat .w64 (.word .w64 7)) = false := by decide

-- Admission checks representability, indices, argument arity, and branch typing.
example : checkProgram [.word .w64 (2^64)] [binarySignature] = false := by decide
example : checkProgram [.var 2] [binarySignature] = false := by decide
example : checkProgram [.call 0 []] [binarySignature] = false := by decide
example : checkProgram [.ifE (.bool true) (.word .w64 1) (.bool false)]
    [binarySignature] = false := by decide
example : checkProgram [chooseBody] [] = false := by decide

-- Source certificates are universal, including modular boundary inputs.
example : Runs [chooseBody] chooseBody (encodeArgs [0, 0xffffffffffffffff])
    (encodeWord 0) := choose_source 0 0xffffffffffffffff
example : Runs [affineBody] affineBody (encodeArgs [0xffffffffffffffff, 0])
    (encodeWord 4) := affine_source 0xffffffffffffffff 0

#print axioms checkShape_sound
#print axioms checkShape_complete
#print axioms checkProgram_iff
#print axioms admitted_type_safety
#print axioms affineCertificate
#print axioms chooseCertificate
