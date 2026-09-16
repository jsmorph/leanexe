namespace LeanExe.KernelCheck

def validateLevels (levels : Array UInt64) (parameterCount root : UInt64) : UInt64 := Id.run do
  if levels.size % 3 != 0 then return 4
  let count := levels.size / 3
  if root.toNat >= count then return 4
  for i in [:count] do
    let tag := levels[i * 3]!
    let a := levels[i * 3 + 1]!
    let b := levels[i * 3 + 2]!
    if tag == 0 then
      if a != 0 || b != 0 then return 4
    else if tag == 1 then
      if a.toNat >= i || b != 0 then return 4
    else if tag == 2 then
      if a >= parameterCount || b != 0 then return 4
    else if tag == 3 || tag == 4 then
      if a.toNat >= i || b.toNat >= i then return 4
    else return 4
  return 0

end LeanExe.KernelCheck
