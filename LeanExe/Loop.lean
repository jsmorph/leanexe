namespace LeanExe

/-- Applies `f` to the indices `0` through `n - 1` in increasing order, threading
a state that starts at `init`. -/
def loop (n : UInt64) (init : α) (f : UInt64 → α → α) : α :=
  Nat.fold n.toNat (fun i _ state => f (UInt64.ofNat i) state) init

end LeanExe
