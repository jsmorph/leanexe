namespace LeanExe

/-- The array of length `n` whose element `i` is `f i`. -/
def build (n : UInt64) (f : UInt64 → α) : Array α :=
  Array.ofFn (n := n.toNat) fun i => f (UInt64.ofNat i)

end LeanExe
