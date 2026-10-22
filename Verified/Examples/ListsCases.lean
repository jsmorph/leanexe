import Verified.Examples.Lists
import Examples.Trees.Cases

namespace Verified.Examples.Lists

open TestSupport.Host

def render (xs : List UInt64) : String := s!"[{", ".intercalate (xs.map toString)}]"

def cases : IO Unit := do
  IO.println s!"lists|empty|chain-u64||{render empty}|0|0"
  let lists := wordArrays ++ ([63, 999, 1000, 4096] : List Nat).map fun n =>
    (List.range n).map fun i => rw (n + i)
  for xs in lists do
    let n := xs.length
    IO.println s!"lists|keep|chain-u64|{chain xs}|{render (keep xs)}|{n}|{n}"
    IO.println s!"lists|keepViaCall|chain-u64|{chain xs}|{render (keepViaCall xs)}|{n}|{n}"
    IO.println s!"lists|first|i64|{chain xs}|{first xs}|{n}|{n}"
    IO.println s!"lists|rest|chain-u64|{chain xs}|{render (rest xs)}|{n - 1}|{n}"
    IO.println s!"lists|rebuild|chain-u64|{chain xs}|{render (rebuild xs)}|{n}|{n}"
    let result := duplicate xs
    IO.println s!"lists|duplicate|list:chain-u64,chain-u64|{chain xs}|{render result.1} {render result.2}|{2 * n}|{2 * n}"
    for x in [0, 7, maxU] do
      IO.println s!"lists|cons|chain-u64|{u x} {chain xs}|{render (cons x xs)}|{n + 1}|{n + 1}"
      let y := maxU - x
      IO.println s!"lists|consTwice|chain-u64|{u x} {u y} {chain xs}|{render (consTwice x y xs)}|{n + 2}|{n + 2}"
      IO.println s!"lists|change|chain-u64|{u x} {chain xs}|{render (change x xs)}|{n}|{n}"
      IO.println s!"lists|foldCons|i64|{u x} {chain xs}|{foldCons x xs}|0|{n + 1}"
    for init in [0, 1, maxU] do
      IO.println s!"lists|foldWord|i64|{chain xs} {u init}|{foldWord xs init}|{n}|{n}"
      IO.println s!"lists|foldBuild|i64|{chain xs} {u init}|{foldBuild xs init}|{n}|{2 * n}"
      let (acc, flag) := foldTuple xs init
      IO.println s!"lists|foldTuple|list:i64,i64|{chain xs} {u init}|{acc} {if flag then 1 else 0}|{n}|{n}"
      for values in [#[], #[maxU], #[0, 3, maxU, 7]] do
        let expected := xs.foldl (fun acc value => acc + values.getD value.toNat 0) init
        IO.println s!"lists|foldLookup|i64|{chain xs} {arrU values.toList} {u init}|{expected}|{n + 1}|{n + 1}"
      for ys in [[], [maxU], [0, 3, maxU]] do
        IO.println s!"lists|foldNested|i64|{chain xs} {chain ys} {u init}|{foldNested xs ys init}|{n + ys.length}|{n + ys.length}"
    for init in [false, true] do
      IO.println s!"lists|foldBool|i64|{chain xs} {u (if init then 1 else 0)}|{if foldBool xs init then 1 else 0}|{n}|{n}"
    for bias in [0, 7, maxU] do
      IO.println s!"lists|foldChoice|i64|{chain xs} {u bias}|{foldChoice xs bias}|{n}|{n}"
    for init in ([0.0, -2.5, 1024.0] : List Float) do
      IO.println s!"lists|foldFloat|f64|{chain xs} f64:{init.toBits}|{(foldFloat xs init).toBits}|{n}|{n}"
    for init in ([0.0, -2.5, 1024.0] : List Float32) do
      IO.println s!"lists|foldFloat32|f32|{chain xs} f32:{init.toBits}|{(foldFloat32 xs init).toBits}|{n}|{n}"
  for xs in [[], [0], [1, 2, 3], [998], [998, 998]] do
    for init in [0, maxU] do
      IO.println s!"lists|foldCalls|i64|{chain xs} {u init}|{foldCalls xs init}|{xs.length}|{xs.length}"
  for xs in [[999], [0, 999]] do
    IO.println s!"lists|foldCalls|i64|{chain xs} i64:7|trap"

end Verified.Examples.Lists
