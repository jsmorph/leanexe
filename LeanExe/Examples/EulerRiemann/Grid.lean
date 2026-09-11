namespace LeanExe.Examples.EulerRiemann

def validSize (n : Nat) : Bool :=
  decide (2 ≤ n ∧ n ≤ 800)

def neighbor (n index : Nat) (axisY forward : Bool) : Nat :=
  let stride := if axisY then n else 1
  let coordinate := if axisY then index / n else index % n
  if forward then
    if coordinate + 1 < n then index + stride else index
  else
    if coordinate = 0 then index else index - stride

def lowerFractionNumerator (n coordinate : Nat) : Nat :=
  min 5 (4 * n - 5 * coordinate)

def growIndices : Nat → Nat → Array UInt64 → Array UInt64
  | 0, size, values => values.extract 0 size
  | fuel + 1, size, values =>
    if size ≤ values.size then values.extract 0 size
    else
      let offset := values.size.toUInt64
      let upper := values.map (fun i => i + offset)
      growIndices fuel size (values ++ upper)

def indices (fuel size : Nat) : Array UInt64 :=
  growIndices fuel size #[0]

def gridIndices (n : Nat) : Array UInt64 :=
  if validSize n then indices 20 (n * n) else #[]

end LeanExe.Examples.EulerRiemann
