import Library.Regex.Program

/-! Random patterns and inputs for the regex tests: pattern trees from a fixed seed over sets of the
bytes 0, 1, 2, 63, 64, 128, 200, and 255, which reach every word of a set, their postfix words,
and inputs over the bytes 0, 1, 64, and 255, packed eight bytes to a word with a word of nonzero
bytes after them. -/

namespace TestSupport.Regex.Generate

/-- A generated pattern tree. -/
inductive T where
  | empty
  | eps
  | cls (w0 w1 w2 w3 : UInt64)
  | cat (a b : T)
  | alt (a b : T)
  | star (a : T)

/-- The postfix words of a pattern tree. -/
def T.words : T → List UInt64
  | .empty => [0]
  | .eps => [1]
  | .cls w0 w1 w2 w3 => [2, w0, w1, w2, w3]
  | .cat a b => a.words ++ b.words ++ [3]
  | .alt a b => a.words ++ b.words ++ [4]
  | .star a => a.words ++ [5]

/-- The next state of a 64-bit linear congruential generator. -/
def next (x : UInt64) : UInt64 := x * 6364136223846793005 + 1442695040888963407

/-- A number below `k` from the state `x`. -/
def pick (x : UInt64) (k : Nat) : Nat := ((x >>> 33).toNat) % k

def classBytes : List UInt8 := [0, 1, 2, 63, 64, 128, 200, 255]

/-- The four words of the set of the bytes of `classBytes` whose bits in `m` are set. -/
def classWords (m : Nat) : UInt64 × UInt64 × UInt64 × UInt64 :=
  (List.range classBytes.length).foldl (fun (w0, w1, w2, w3) i =>
    if m.testBit i then
      let b := (classBytes.getD i 0).toNat
      let bit : UInt64 := (1 : UInt64) <<< (b % 64).toUInt64
      if b < 64 then (w0 ||| bit, w1, w2, w3) else if b < 128 then (w0, w1 ||| bit, w2, w3)
      else if b < 192 then (w0, w1, w2 ||| bit, w3) else (w0, w1, w2, w3 ||| bit)
    else (w0, w1, w2, w3)) (0, 0, 0, 0)

/-- A random leaf, and the next state. -/
def genLeaf (x : UInt64) : T × UInt64 :=
  let x := next x
  match pick x 8 with
  | 0 => (.empty, x)
  | 1 => (.eps, x)
  | _ =>
    let x := next x
    let (w0, w1, w2, w3) := classWords (pick x 256)
    (.cls w0 w1 w2 w3, x)

/-- A random tree of depth at most `depth`, and the next state. -/
def gen : Nat → UInt64 → T × UInt64
  | 0, x => genLeaf x
  | d + 1, x =>
    let x := next x
    match pick x 6 with
    | 0 => genLeaf x
    | 1 => let (a, x) := gen d x; (.star a, x)
    | 2 | 3 => let (a, x) := gen d x; let (b, x) := gen d x; (.cat a b, x)
    | _ => let (a, x) := gen d x; let (b, x) := gen d x; (.alt a b, x)

/-- Bytes packed eight to a word in little-endian order, followed by a word of nonzero bytes. -/
def pack (bytes : List UInt8) : Array UInt64 :=
  let n := bytes.length
  ((List.range ((n + 7) / 8 + 1)).map fun w =>
    (List.range 8).foldl (fun acc j =>
      let i := 8 * w + j
      acc ||| ((if i < n then (bytes.getD i 0).toUInt64 else 0xA5) <<< (8 * j).toUInt64)) 0).toArray

def inputBytes : List UInt8 := [0, 1, 64, 255]

/-- Every string of length at most `k` over `inputBytes`. -/
def inputs : Nat → List (List UInt8)
  | 0 => [[]]
  | k + 1 => [[]] ++ (inputs k).flatMap fun s => inputBytes.map (· :: s)

end TestSupport.Regex.Generate
