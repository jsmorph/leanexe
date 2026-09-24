namespace LeanExe
namespace Examples.TalosGcd

-- Preserve the audited artifact across Lean 4.34's `do` elaborator transition.
set_option backward.do.legacy true in
def gcd (a b : UInt64) : UInt64 := Id.run do
  let mut x := a
  let mut y := b
  while y != 0 do
    let r := x % y
    x := y
    y := r
  return x

end Examples.TalosGcd
end LeanExe
