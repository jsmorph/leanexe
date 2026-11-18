import Demos.RandomHistogram.Program
import Verified.Reflect.Command

namespace Demos.RandomHistogram

open Library.Numerics.Decimal.Int64Text

verified_compile compiled :=
  [parseStep, parseN, countWord, histogram, digitCount, digitByte, appendLine, render]

end Demos.RandomHistogram
