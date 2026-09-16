namespace LeanExe.KernelCheck

/-- Three words per node: tag, first payload, second payload. Node IDs are
zero-based. Tags: 0 sort, 1 bvar, 2 Pi, 3 lambda. Children precede parents. -/
def validateGraph (g : Array UInt64) (root : UInt64) : UInt64 := Id.run do
  if g.size % 3 != 0 then return 4
  let count := g.size / 3
  if root.toNat >= count then return 4
  for i in [:count] do
    let tag := g[i * 3]!
    let a := g[i * 3 + 1]!
    let b := g[i * 3 + 2]!
    if tag == 0 || tag == 1 then
      if b != 0 then return 4
    else if tag == 2 || tag == 3 then
      if a.toNat >= i || b.toNat >= i then return 4
    else return 4
  return 0

end LeanExe.KernelCheck
