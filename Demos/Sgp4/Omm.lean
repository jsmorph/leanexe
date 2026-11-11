import Demos.Sgp4.Box
import Library.Numerics.Decimal.ParseFloat.Program

/-!
A reader of the decimal values of an Orbit Mean-Elements Message.  `field` reads the text of one
value, such as the text after `MEAN_MOTION =`, with the library's `parse64` and returns the
interval from one step below the rounded value to one step above it.  `OmmSound.lean` proves that
the interval contains the decimal number that the text denotes.  The seven intervals of
`MEAN_MOTION`, `ECCENTRICITY`, `INCLINATION`, `RA_OF_ASC_NODE`, `ARG_OF_PERICENTER`,
`MEAN_ANOMALY`, and `BSTAR` are the arguments of `sgp4Box`.  `fieldNonneg` reads the values that
cannot be negative, such as the eccentricity, so that the eccentricity 0 has an interval that
starts at 0.  `field` accepts every text of the general grammar of `parse64`: decimal and
hexadecimal numbers, whose intervals contain them, and infinities and NaNs, whose intervals are
rejected.
-/

namespace Demos.Sgp4.Omm

open Library.Numerics.Interval Library.Numerics.Decimal

/-- The interval around the binary64 value of the decimal number of a text, an array of words
that hold one byte each.  A text that is no number of the grammar of `parse64` is rejected. -/
def field (text : Array UInt64) : Interval :=
  let r := ParseFloat.parse64 true text
  if r.1 then around (Float.ofBits r.2) else rejected

/-- `field` for a value with a sign only when its text begins with `-`: the interval of a text
that does not begin with `-` is clamped at 0, so the decimal 0 has the interval from 0 to the
smallest positive float. -/
def fieldNonneg (text : Array UInt64) : Interval :=
  let a := field text
  if text[(0 : UInt64).toNat]! == 45 then a else clamp a 0.0 a.hi

end Demos.Sgp4.Omm
