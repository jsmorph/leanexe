import Examples.Words.Program
import TestSupport.Host

/-! The conversion of a list to `Words`, which the verified compiler's cases use. -/

namespace Examples.Words

open TestSupport.Host

def Words.ofList : List UInt64 → Words
  | [] => .nil
  | x :: xs => .cons x (Words.ofList xs)

end Examples.Words
