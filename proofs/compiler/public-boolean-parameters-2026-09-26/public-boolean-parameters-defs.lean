def publicFlagWord (flag : Bool) (x : UInt64) : UInt64 :=
  if flag then x + 7 else x - 3

def publicWordFlag (x : UInt64) (flag : Bool) : UInt64 :=
  x * 11 + flag.toUInt64

def publicFlagsWord (left right : Bool) : UInt64 :=
  left.toUInt64 * 3 + right.toUInt64 * 7

def publicFlagResult (flag : Bool) (x : UInt64) : Bool := flag && x != 0

def publicWordFlagResult (x : UInt64) (flag : Bool) : Bool := !flag || x == 7

def publicFlagsResult (left right : Bool) : Bool := left != right

def publicFlagLet (flag : Bool) (x : UInt64) : UInt64 :=
  let saved := !flag
  let n := x + flag.toUInt64
  if saved then n / x else n % x

def publicFlagBind (x : UInt64) (flag : Bool) : Id UInt64 := do
  let saved ← pure (!flag)
  let n ← pure (x + saved.toUInt64)
  return if flag then n + 3 else n - 5

def publicFlagCapture (flag : Bool) (x : UInt64) : Bool :=
  let f := fun b : Bool => b && flag
  let g := fun n : UInt64 => f (n != x)
  g (x + 1)

def publicFlagsDecision (left right : Bool) : Id (Id Bool) :=
  pure (pure (decide (left = right ∨ ¬ left)))

