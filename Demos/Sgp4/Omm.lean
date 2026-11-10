import Demos.Sgp4.Box
import Library.Numerics.Decimal.ParseFloat.Program

/-!
A reader of the decimal values of an Orbit Mean-Elements Message.  `field` reads the text of one
value, such as the text after `MEAN_MOTION =`, with the library's `parse64` and returns the
interval from one step below the rounded value to one step above it.  `OmmSound.lean` proves that
the interval contains the decimal number that the text denotes.  The seven intervals of
`MEAN_MOTION`, `ECCENTRICITY`, `INCLINATION`, `RA_OF_ASC_NODE`, `ARG_OF_PERICENTER`,
`MEAN_ANOMALY`, and `BSTAR` are the arguments of `sgp4Box`.
-/

namespace Demos.Sgp4.Omm

open Library.Numerics.Interval Library.Numerics.Decimal

/-- The interval around the binary64 value of the decimal number of a text, an array of words
that hold one byte each.  A text that is no number of the grammar of `parse64` is rejected. -/
def field (text : Array UInt64) : Interval :=
  let r := ParseFloat.parse64 true text
  if r.1 then around (Float.ofBits r.2) else rejected

end Demos.Sgp4.Omm
