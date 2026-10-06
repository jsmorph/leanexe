import Examples.Words.Program
import Examples.Host

/-! The module cases of `words`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Words

open Examples.Host

def Words.ofList : List UInt64 → Words
  | [] => .nil
  | x :: xs => .cons x (Words.ofList xs)

def Words.toList : Words → List UInt64
  | .nil => []
  | .cons x w => x :: Words.toList w

def wordsCases : IO Unit := do
  let lists : List (List UInt64) := [[], [0], [maxU], [7, 8, 9], (List.range 50).map rw]
  for xs in lists do
    line "words" "first" "i64" [chain xs] (toString (Words.ofList xs).first)
    for acc in [0, 5, maxU] do
      line "words" "sumAcc" "i64" [u acc, chain xs] (toString (Words.sumAcc acc (Words.ofList xs)))
  for n in [0, 1, 2, 7, 64, 300] do
    line "words" "range" "chain-u64" [u n] (words (Words.toList (Words.range n)))

def cases : IO Unit := do
  wordsCases

end Examples.Words
