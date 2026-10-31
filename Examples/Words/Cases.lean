import Examples.Words.Program
import TestSupport.Host

/-! The conversions between lists and `Words`, which the verified compiler's cases use. -/

namespace Examples.Words

open TestSupport.Host

def Words.ofList : List UInt64 → Words
  | [] => .nil
  | x :: xs => .cons x (Words.ofList xs)

def Words.toList : Words → List UInt64
  | .nil => []
  | .cons x w => x :: Words.toList w

end Examples.Words
