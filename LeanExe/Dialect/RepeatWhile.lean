namespace LeanExe

/-- Applies `step` to a state that starts at `init` while `cond` holds, at most `fuel` times. -/
def repeatWhile (fuel : UInt64) (init : α) (cond : α → Bool) (step : α → α) : α :=
  go fuel.toNat init
where
  go : Nat → α → α
    | 0, s => s
    | k + 1, s => if cond s then go k (step s) else s

end LeanExe
