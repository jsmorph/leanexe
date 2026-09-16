import Project.ExpWide.Model

namespace Project.Softmax

def maximum (a b : UInt64) : UInt64 :=
  if a < 0x8000000000000000 then
    if b < 0x8000000000000000 then (if a ≤ b then b else a) else a
  else
    if b < 0x8000000000000000 then b else (if a ≤ b then a else b)

def bounded (x : UInt64) : Bool :=
  decide (x &&& 0x7FFFFFFFFFFFFFFF ≤ 0x4010000000000000)

def inDomain (n a b c d : UInt64) : Bool :=
  decide (0 < n) && decide (n ≤ 4) && bounded a && bounded b && bounded c && bounded d

def activeScore (n i x first : UInt64) : UInt64 := if i < n then x else first

def weight (n i x m : UInt64) : UInt64 :=
  if i < n then ExpWide.evaluate (Wasm.IEEE64.sub x m) else 0

def probability (n i w total : UInt64) : UInt64 :=
  if i < n then Wasm.IEEE64.div w total else 0

structure Result where
  status : UInt64
  p0 : UInt64
  p1 : UInt64
  p2 : UInt64
  p3 : UInt64
  deriving DecidableEq, Inhabited

def rowMaximum (n a b c d : UInt64) : UInt64 :=
  maximum (maximum a (activeScore n 1 b a))
    (maximum (activeScore n 2 c a) (activeScore n 3 d a))

def total (w0 w1 w2 w3 : UInt64) : UInt64 :=
  Wasm.IEEE64.add (Wasm.IEEE64.add w0 w1) (Wasm.IEEE64.add w2 w3)

def compute (n a b c d : UInt64) : Result :=
  let m := rowMaximum n a b c d
  let w0 := weight n 0 a m
  let w1 := weight n 1 b m
  let w2 := weight n 2 c m
  let w3 := weight n 3 d m
  let s := total w0 w1 w2 w3
  ⟨0, probability n 0 w0 s, probability n 1 w1 s,
    probability n 2 w2 s, probability n 3 w3 s⟩

def softmax (n a b c d : UInt64) : Result :=
  if inDomain n a b c d then compute n a b c d else ⟨1, 0, 0, 0, 0⟩

end Project.Softmax
