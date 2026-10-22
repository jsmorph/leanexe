namespace Library.Numerics.Bounds

abbrev absBits (bits : UInt64) : UInt64 := bits &&& 0x7FFFFFFFFFFFFFFF

/-- Neither infinite nor NaN. -/
abbrev finite (x : Float) : Bool := absBits x.toBits < 0x7FF0000000000000

/-- A checked value: status 0 with a value, or status 1. -/
structure Checked where
  status : UInt64
  value : Float
  deriving Inhabited

abbrev rejectedChecked : Checked := ⟨1, 0⟩

/-- The next binary64 word above `bits` in value. -/
abbrev nextUpBits (bits : UInt64) : UInt64 :=
  if bits == 0x8000000000000000 then 1 else if bits < 0x8000000000000000 then bits + 1
  else bits - 1

/-- The next binary64 word below `bits` in value. -/
abbrev nextDownBits (bits : UInt64) : UInt64 :=
  if bits == 0 then 0x8000000000000001 else if bits < 0x8000000000000000 then bits - 1
  else bits + 1

/-- A rounded result moved one step up or down, when the result and the step are finite. -/
def endpoint (up : Bool) (rounded : Float) : Checked :=
  let bits := if up then nextUpBits rounded.toBits else nextDownBits rounded.toBits
  if finite rounded && absBits bits < 0x7FF0000000000000 then ⟨0, Float.ofBits bits⟩
  else rejectedChecked

def outAdd (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a + b)
  if finite a && finite b && e.status == 0 then e else rejectedChecked

def outSub (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a - b)
  if finite a && finite b && e.status == 0 then e else rejectedChecked

def outMul (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a * b)
  if finite a && finite b && e.status == 0 then e else rejectedChecked

def outDiv (up : Bool) (a b : Float) : Checked :=
  let e := endpoint up (a / b)
  if finite a && finite b && 0 < absBits b.toBits && e.status == 0 then e else rejectedChecked

def outSqrt (up : Bool) (a : Float) : Checked :=
  let e := endpoint up a.sqrt
  if finite a && a.toBits ≤ 0x8000000000000000 && e.status == 0 then e else rejectedChecked

end Library.Numerics.Bounds
