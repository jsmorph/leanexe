import LeanExe.Float64

namespace LeanExe.Examples.Float64Bits

def addBits (left right : UInt64) : UInt64 :=
  LeanExe.Float64.addBits left right

def mulBits (left right : UInt64) : UInt64 :=
  LeanExe.Float64.mulBits left right

def mulThenAddBits (left right addend : UInt64) : UInt64 :=
  LeanExe.Float64.addBits (LeanExe.Float64.mulBits left right) addend

def addMulBits (addend left right : UInt64) : UInt64 :=
  LeanExe.Float64.addBits addend (LeanExe.Float64.mulBits left right)

/-- Two-word public result for guarded floating-point kernels.  Status zero
means that `bits` contains a computed binary64 result; status one means that an
input failed the raw-bit domain check and `bits` is zero. -/
structure CheckedBits where
  status : UInt64
  bits : UInt64
  deriving Inhabited

/-- The sign-cleared binary64 encoding is at most the encoding of one half. -/
def boundedByHalf (bits : UInt64) : Bool :=
  decide ((bits &&& 0x7FFFFFFFFFFFFFFF) ≤ 0x3FE0000000000000)

/-- Guarded two-term binary64 dot product over raw bit patterns. -/
def dot2CheckedBits (a₀ b₀ a₁ b₁ : UInt64) : CheckedBits :=
  if boundedByHalf a₀ && boundedByHalf b₀ &&
      boundedByHalf a₁ && boundedByHalf b₁ then
    { status := 0
      bits := LeanExe.Float64.addBits
        (LeanExe.Float64.mulBits a₀ b₀)
        (LeanExe.Float64.mulBits a₁ b₁) }
  else
    { status := 1, bits := 0 }

/-- Guarded quadratic Horner evaluation over raw binary64 bit patterns.
The accepted path computes `(c₂ * x + c₁) * x + c₀` with two rounded
multiplications and two rounded additions. -/
def horner2CheckedBits (x c₂ c₁ c₀ : UInt64) : CheckedBits :=
  if boundedByHalf x && boundedByHalf c₂ &&
      boundedByHalf c₁ && boundedByHalf c₀ then
    { status := 0
      bits := LeanExe.Float64.addBits
        (LeanExe.Float64.mulBits
          (LeanExe.Float64.addBits
            (LeanExe.Float64.mulBits c₂ x)
            c₁)
          x)
        c₀ }
  else
    { status := 1, bits := 0 }

/-- Runtime-length binary64 dot product over raw-bit arrays.  Unequal lengths
are rejected.  The numerical theorem states the finite-domain and headroom
requirements explicitly rather than relying on native floating-point checks. -/
def dotCheckedBits (left right : Array UInt64) : CheckedBits :=
  if left.size != right.size then
    { status := 1, bits := 0 }
  else if left.isEmpty then
    { status := 0, bits := 0 }
  else
    Id.run do
      let mut index := 1
      let mut bits := LeanExe.Float64.mulBits left[0]! right[0]!
      while index < left.size do
        bits := LeanExe.Float64.addBits bits
          (LeanExe.Float64.mulBits left[index]! right[index]!)
        index := index + 1
      return { status := 0, bits }

end LeanExe.Examples.Float64Bits
