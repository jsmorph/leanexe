namespace LeanExe.KernelCheck

/-- M0.0: check `Sort level : Sort claimedLevel` for concrete universe levels.

Return 0 for acceptance, 1 for an incorrect claimed type, and 2 when the
successor level is outside this initial UInt64 representation. These are
returned words, not process exit codes. No declaration or proof is checked.
-/
def checkSort (level claimedLevel : UInt64) : UInt64 :=
  if level == 18446744073709551615 then
    2
  else if claimedLevel == level + 1 then
    0
  else
    1

end LeanExe.KernelCheck
