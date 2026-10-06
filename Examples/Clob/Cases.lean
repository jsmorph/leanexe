import Examples.Clob.Program
import Examples.Host

/-! The module cases of `clob`, one line per case in the format of
`tests/modules/run.sh`. -/

namespace Examples.Clob

open Examples.Host

/-- A book of `n` levels with descending prices from `top`, and sizes. -/
def book (n top seed : Nat) : List UInt64 × List UInt64 :=
  ((List.range n).map fun k => UInt64.ofNat (top - 3 * k - (seed + k) % 3),
    (List.range n).map fun k => 1 + below 20 (seed + 5 * k))

def books : List (List UInt64 × List UInt64) :=
  [([], []), ([100], [5]), ([105, 102, 101, 100, 98], [4, 4, 6, 7, 10]), ([100, 98], [5]),
   ([100], [5, 6]), ([100, 99], [maxU, 2])] ++
    (List.range 30).map fun i => book (i % 9) (200 + 7 * i) i

/-- An output array of up to two words, to which `stepCommand` and `runOut` append. -/
def outputs (i : Nat) : List UInt64 := (List.range (i % 3)).map fun k => UInt64.ofNat (7 + k)

def clobCases : IO Unit := do
  for (i, (ps, ss)) in (List.range books.length).zip books do
    let p := ps.toArray
    let s := ss.toArray
    let n := ps.length
    let ks : List UInt64 := [0, UInt64.ofNat (n / 2), UInt64.ofNat n, UInt64.ofNat (n + 2)]
    let prices : List UInt64 :=
      [0, 99, 100, 150, maxU] ++ (if n > 0 then [ps[0]!, ps[n - 1]!, ps[0]! + 1] else [])
    line "clob" "marketBuy" "array-u64" [arrU ps, arrU ss, u (below 60 i)]
      (words (Examples.Clob.marketBuy p s (below 60 i)).toList)
    for k in ks do
      line "clob" "fillLevel" "array-u64" [arrU ss, u k, u (below 8 (i + k.toNat))]
        (words (Examples.Clob.fillLevel s k (below 8 (i + k.toNat))).toList)
      line "clob" "fillTwice" "array-u64" [arrU ss, u k, u (below 8 (i + k.toNat)), u 1]
        (words (Examples.Clob.fillTwice s k (below 8 (i + k.toNat)) 1).toList)
      let fk := Examples.Clob.fillKeep s k (below 8 (i + k.toNat))
      line "clob" "fillKeep" "list:array-u64,array-u64" [arrU ss, u k, u (below 8 (i + k.toNat))]
        s!"{words fk.1.toList},{words fk.2.toList}"
      line "clob" "insertLevel" pairKind [arrU ps, arrU ss, u k, u 97, u 3]
        (pair (Examples.Clob.insertLevel p s k 97 3))
      line "clob" "setLevel" pairKind [arrU ps, arrU ss, u k, u 9]
        (pair (Examples.Clob.setLevel p s k 9))
      line "clob" "removeLevel" pairKind [arrU ps, arrU ss, u k]
        (pair (Examples.Clob.removeLevel p s k))
    for price in prices do
      line "clob" "findLevel" "i64" [arrU ps, u price] (toString (Examples.Clob.findLevel p price))
      line "clob" "depth" "i64" [arrU ps, arrU ss, u price]
        (toString (Examples.Clob.depth p s price))
      line "clob" "addBid" pairKind [arrU ps, arrU ss, u price, u 4]
        (pair (Examples.Clob.addBid p s price 4))
      line "clob" "cancelBid" pairKind [arrU ps, arrU ss, u price, u (below 12 (i + price.toNat))]
        (pair (Examples.Clob.cancelBid p s price (below 12 (i + price.toNat))))
      for kind in [0, 1, 2] do
        line "clob" "applyCommand" pairKind [arrU ps, arrU ss, u kind, u price, u 5]
          (pair (Examples.Clob.applyCommand p s kind price 5))
        line "clob" "stepCommand" tripleKind [arrU ps, arrU ss, arrU (outputs i), u kind, u price, u 5]
          (triple (Examples.Clob.stepCommand p s (outputs i).toArray kind price 5))

/-- Commands of the three kinds against prices near the book `ps`, three words each. -/
def commandList (ps : List UInt64) (count seed : Nat) : List UInt64 :=
  (List.range count).flatMap fun j =>
    let kind := below 3 (seed + 7 * j)
    let near := if ps.isEmpty then 100 else ps[(seed + j) % ps.length]!
    let price := if (seed + j) % 4 = 0 then near + 1 else near
    [kind, price, 1 + below 9 (seed + 3 * j)]

def runCases : IO Unit := do
  for (i, (ps, ss)) in (List.range books.length).zip books do
    for count in [0, 1, 4, 13] do
      let cs := commandList ps count i
      line "clob" "runCommands" pairKind [arrU ps, arrU ss, arrU cs]
        (pair (Examples.Clob.runCommands ps.toArray ss.toArray cs.toArray))
      line "clob" "runOut" tripleKind [arrU ps, arrU ss, arrU (outputs i), arrU cs]
        (triple (Examples.Clob.runOut ps.toArray ss.toArray (outputs i).toArray cs.toArray))
    -- A trailing partial command is ignored.
    let cs := commandList ps 2 i ++ [0, 5]
    line "clob" "runCommands" pairKind [arrU ps, arrU ss, arrU cs]
      (pair (Examples.Clob.runCommands ps.toArray ss.toArray cs.toArray))
    line "clob" "runOut" tripleKind [arrU ps, arrU ss, arrU (outputs i), arrU cs]
      (triple (Examples.Clob.runOut ps.toArray ss.toArray (outputs i).toArray cs.toArray))

def cases : IO Unit := do
  clobCases
  runCases

end Examples.Clob
