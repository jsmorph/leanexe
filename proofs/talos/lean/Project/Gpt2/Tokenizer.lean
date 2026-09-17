import Init

/-! GPT-2 byte BPE. The host supplies packed vocabulary, merge, and Unicode
category tables; UTF-8 parsing, pre-token splitting, and BPE execute in Wasm.
No artifact correctness theorem is claimed for this demo tokenizer. -/
namespace Project.Gpt2.Tokenizer

def width (b : UInt64) : Nat :=
  if b < 128 then 1 else if b < 224 then 2 else if b < 240 then 3 else 4

def codepoint (input : Array UInt64) (i : Nat) : UInt64 := Id.run do
  let b := input[i]!
  if b < 128 then return b
  if b < 194 || b > 244 then return 0x110000
  let n := width b
  if i+n > input.size then return 0x110000
  let mut cp := b &&& (if n == 2 then 31 else if n == 3 then 15 else 7)
  for j in [1:n] do
    let c := input[i+j]!
    if c < 128 || c > 191 then return 0x110000
    cp := (cp <<< 6) ||| (c &&& 63)
  if (n == 3 && cp < 2048) || (n == 4 && cp < 65536) ||
      (cp ≥ 0xD800 && cp ≤ 0xDFFF) || cp ≥ 0x110000 then return 0x110000
  return cp

def category (table input : Array UInt64) (i : Nat) : UInt64 :=
  table[table[3]!.toNat+(codepoint input i).toNat]!

def contraction (x : Array UInt64) (i : Nat) : Nat :=
  if x[i]! != 39 then 0
  else if i+1 < x.size && (x[i+1]! == 115 || x[i+1]! == 116 || x[i+1]! == 109 || x[i+1]! == 100) then 2
  else if i+2 < x.size && ((x[i+1]! == 114 && x[i+2]! == 101) ||
      (x[i+1]! == 118 && x[i+2]! == 101) || (x[i+1]! == 108 && x[i+2]! == 108)) then 3
  else 0

def pieceEnd (table input : Array UInt64) (start : Nat) : Nat := Id.run do
  let c := contraction input start
  if c > 0 then return start+c
  let mut i := start
  -- The regex's optional prefix is a literal ASCII space, not arbitrary whitespace.
  if input[i]! == 32 && i+1 < input.size && category table input (i+1) != 3 then i := i+1
  let kind := category table input i
  let mut last := i
  for _ in [:input.size] do
    if i ≥ input.size || category table input i != kind then break
    last := i
    i := i + width input[i]!
  -- \s+(?!\S) consumes all but the final whitespace before a nonspace.
  if kind == 3 && i < input.size && last > start then return last
  return i

def lookup (table : Array UInt64) (left right : UInt64) : UInt64 := Id.run do
  let key := left*65536+right+1
  let mut slot := (((left*65599) ^^^ right)*2654435761) &&& 131071
  for _ in [:131072] do
    let offset := table[2]!.toNat+2*slot.toNat
    let stored := table[offset]!
    if stored == 0 then return 0
    if stored == key then return table[offset+1]!
    slot := (slot+1) &&& 131071
  return 0

def bpe (table : Array UInt64) (piece : Array UInt64) : Array UInt64 := Id.run do
  let mut tokens := piece.map fun b => table[8+b.toNat]!
  for _ in [:piece.size] do
    let mut best := 50257
    let mut bestIndex := 0
    for j in [:tokens.size-1] do
      let merged := lookup table tokens[j]! tokens[j+1]!
      if merged != 0 && merged < best then
        best := merged
        bestIndex := j
    if best == 50257 then break
    let mut next := #[]
    for j in [:tokens.size] do
      if j == bestIndex then next := next.push best
      else if j != bestIndex+1 then next := next.push tokens[j]!
    tokens := next
  return tokens

def pieceTokens (table input : Array UInt64) (start stop : Nat) : Array UInt64 := Id.run do
  let mut piece := #[]
  for j in [start:stop] do piece := piece.push input[j]!
  return bpe table piece

def appendTokens (out tokens : Array UInt64) : Array UInt64 :=
  out ++ tokens

def encode (table input : Array UInt64) : Array UInt64 := Id.run do
  let mut i := 0
  for _ in [:input.size] do
    if i ≥ input.size then break
    if codepoint input i ≥ 0x110000 then return #[0xFFFFFFFFFFFFFFFF]
    i := i+width input[i]!
  let mut out := #[]
  i := 0
  for _ in [:input.size] do
    if i ≥ input.size then break
    let stop := pieceEnd table input i
    out := appendTokens out (pieceTokens table input i stop)
    i := stop
  return out

def decode (table input : Array UInt64) : Array UInt64 := Id.run do
  let mut out := #[]
  for token in input do
    if token ≥ 50257 then return #[0xFFFFFFFFFFFFFFFF]
    let start := table[table[4]!.toNat+token.toNat]!.toNat
    let stop := table[table[4]!.toNat+token.toNat+1]!.toNat
    for j in [start:stop] do out := out.push table[table[5]!.toNat+j]!
  return out

def tokens (op : UInt64) (table input : Array UInt64) : Array UInt64 :=
  if op == 0 then encode table input else if op == 1 then decode table input
  else #[]

end Project.Gpt2.Tokenizer
