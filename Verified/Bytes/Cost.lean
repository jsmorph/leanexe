namespace Verified.Bytes

def allocationCost (count : Nat) : Nat :=
  if count = 0 then 0 else 48 + 8 * max 1 ((count + 7) / 8)

end Verified.Bytes
