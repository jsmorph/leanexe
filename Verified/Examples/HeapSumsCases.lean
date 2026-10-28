import Verified.Examples.HeapSums
import Examples.Trees.Cases

/-! The cases of the sums that hold heap values.  The host passes an `Item` as its tuple: the tag,
the bytes, the array, the scale, the tree, and the weight.  An active text is a block of the
host's, and an inactive one the words `0 0` of `Bytes.empty`; an array, active or not, is a block
of the host's, as the `#[]` of the instance is; and an inactive tree is null.

The block counts follow the code: a construction of a text, a tree, or an empty item allocates the
`#[]` of its words, a copy of an item allocates one block for its array, one for its bytes when
they are not empty, and one for each node of its tree, and a match on an owned item releases the
components that its branch does not use.  A borrowed parameter keeps the host's blocks. -/

namespace Verified.Examples.HeapSums

open LeanExe.Pipeline TestSupport.Host Examples.Trees Library.Trees.WordTree

def hex (b : LeanExe.Bytes) : String :=
  String.join (b.data.toList.map fun byte =>
    let digits := Nat.toDigits 16 byte.toNat
    String.mk (if digits.length < 2 then '0' :: digits else digits))

def arrayText (xs : Array UInt64) : String := ",".intercalate (xs.toList.map toString)

def arrayOut (xs : Array UInt64) : String :=
  "[" ++ ", ".intercalate (xs.toList.map toString) ++ "]"

/-- The host's arguments for an item. -/
def itemArg : Item → String
  | .text b => s!"i64:0 bytes:{hex b} array-u64: i64:0 tree-u64:. f64:0"
  | .words xs scale => s!"i64:1 i64:0 i64:0 array-u64:{arrayText xs} i64:{scale} tree-u64:. f64:0"
  | .keys t w => s!"i64:2 i64:0 i64:0 array-u64: i64:0 tree-u64:{KeyTree.describe t} \
      f64:{w.toBits}"
  | .none => "i64:3 i64:0 i64:0 array-u64: i64:0 tree-u64:. f64:0"

def itemKind : String := "list:i64,bytes,array-u64,i64,tree-u64,f64"

/-- The host's output for an item: its tuple, one component per item of `itemKind`. -/
def itemOut (i : Item) : String :=
  let (tag, b, xs, scale, t, w) := Flat.flat i
  s!"{tag} {hex b} {arrayOut xs} {scale} {KeyTree.describe t} {w.toBits}"

/-- The blocks of the host's representation of an item. -/
def hostBlocks : Item → Nat
  | .text _ => 2
  | .words _ _ => 1
  | .keys t _ => 1 + t.size.toNat
  | .none => 1

/-- The blocks that a copy of an item allocates. -/
def copyBlocks : Item → Nat
  | .text b => (if b.size = 0 then 0 else 1) + 1
  | .words _ _ => 1
  | .keys t _ => 1 + t.size.toNat
  | .none => 1

def longText : LeanExe.Bytes := ⟨⟨(List.range 40).toArray.map UInt8.ofNat⟩⟩

def longWords : Array UInt64 := (List.range 30).toArray.map rw

def texts : List LeanExe.Bytes := [.empty, bytes![0], bytes![1, 2, 3, 255], longText]

def wordLists : List (Array UInt64) := [#[], #[5], #[1, 2, 3, maxU], longWords]

def trees : List KeyTree := [.leaf, .node .leaf 5 .leaf, KeyTree.arbitrary 6 3, KeyTree.chain 20]

def items : List Item :=
  texts.map .text ++ (wordLists.flatMap fun xs => [Item.words xs 0, .words xs 3]) ++
    (trees.flatMap fun t => [Item.keys t 0, .keys t 2.75]) ++ [.none]

def cellArg : Cell → String
  | .chain xs => s!"i64:0 {chain xs} i64:0"
  | .count n => s!"i64:1 chain-u64: i64:{n}"

def cellOut (c : Cell) : String :=
  let (tag, xs, n) := Flat.flat c
  s!"{tag} [{", ".intercalate (xs.map toString)}] {n}"

def cases : IO Unit := do
  for k in [0, 1, 2, 3, maxU] do
    let inputs : List (LeanExe.Bytes × Array UInt64 × KeyTree) :=
      [(bytes![1, 2, 3, 255], #[1, 2, 3, maxU], KeyTree.arbitrary 6 3), (.empty, #[], .leaf),
        (longText, longWords, KeyTree.chain 20)]
    for (b, xs, t) in inputs do
      let n := t.size.toNat
      let args := s!"i64:{k} bytes:{hex b} array-u64:{arrayText xs} tree-u64:{KeyTree.describe t}"
      let placeholder := if k = 1 then 0 else 1
      let live := if k = 0 then 2 else if k = 1 then 1 else if k = 2 then n + 1 else 1
      IO.println s!"heapsums|make|{itemKind}|{args}|{itemOut (make k b xs t)}|{live}|\
        {2 + n + placeholder}"
      IO.println s!"heapsums|extract|array-u64|{args}|{arrayOut (extract k b xs t)}|1|\
        {2 + n + 2 * placeholder}"
      IO.println s!"heapsums|consume|i64|{args}|{consume k b xs t}|0|{2 + n + placeholder}"
  for i in items do
    let host := hostBlocks i
    let arg := itemArg i
    IO.println s!"heapsums|measure|i64|{arg}|{measure i}|{host}|{host}"
    let text := match i with
      | .text b => if b.size = 0 then 0 else 1
      | _ => 0
    IO.println s!"heapsums|textOf|bytes|{arg}|{hex (textOf i)}|{host + text}|{host + text}"
    let rescaled := match i with
      | .words _ _ => 1
      | _ => copyBlocks i
    IO.println s!"heapsums|rescale|{itemKind}|{arg}|{itemOut (rescale i)}|{host + rescaled}|\
      {host + rescaled}"
    for n in [0, 7] do
      let (j, w) := tally i n
      IO.println s!"heapsums|tally|{itemKind},i64|{arg} i64:{n}|{itemOut j} {w}|\
        {host + copyBlocks i}|{host + copyBlocks i}"
    -- Each step of `grow` copies the state and releases the copy's unused components.  A words
    -- item's push then may move the copied array, so a step allocates at most two blocks.  Each
    -- step of `regrow` allocates the empty array of a rebuilt constructor, or at most one block
    -- for the push.
    for n in [0, 1, 5, 100] do
      let steps := n.toNat
      let start := host + copyBlocks i
      let growStep := match i with
        | .words _ _ => 2
        | _ => copyBlocks i
      IO.println s!"heapsums|grow|{itemKind}|i64:{n} {arg}|{itemOut (grow n i)}|{start}|\
        {start + growStep * steps}"
      IO.println s!"heapsums|regrow|{itemKind}|i64:{n} {arg}|{itemOut (regrow n i)}|{start}|\
        {start + steps}"
    let converted := match i with
      | .text _ => 1
      | .words xs _ => (if xs.size = 0 then 0 else 1) + 1
      | .keys t _ => t.size.toNat + 1
      | .none => 1
    IO.println s!"heapsums|convert|{itemKind}|{arg}|{itemOut (convert i)}|{host + converted}|\
      {host + converted}"
  for xs in [[], [7], [1, 2, 3, maxU], (List.range 50).map rw] do
    for k in [0, 1, maxU] do
      let n := xs.length
      IO.println s!"heapsums|cellOf|list:i64,chain-u64,i64|i64:{k} {chain xs}|\
        {cellOut (cellOf k xs)}|{if k = 0 then n else 0}|{n}"
    for c in [Cell.chain xs, .count xs.length.toUInt64] do
      let n := match c with
        | .chain xs => xs.length
        | .count _ => 0
      IO.println s!"heapsums|cellTotal|i64|{cellArg c}|{cellTotal c}|{n}|{n}"
      IO.println s!"heapsums|cellSize|i64|{cellArg c}|{cellSize c}|{n}|{n}"
  -- `cellSize` runs at depth 0 and the guarded `total` at depths 1 to `n + 1` on `n` cells, so
  -- 998 cells return and 999 cells reach depth 1,000.
  for n in [998, 999, 1000] do
    let c := Cell.chain ((List.range n).map UInt64.ofNat)
    if n < 999 then IO.println s!"heapsums|cellSize|i64|{cellArg c}|{cellSize c}|{n}|{n}"
    else IO.println s!"heapsums|cellSize|i64|{cellArg c}|trap"

end Verified.Examples.HeapSums
