import Library.Hashing.Sha256.Program
import Library.Hashing.Sha512.Program
import Library.Hashing.Sha2.Spec

/-! A native check of SHA-256 and SHA-224 in `Library.Hashing.Sha256` and the SHA-512 family in
`Library.Hashing.Sha512` on the NIST CAVP vectors in `data/hashing/sha2/`: every short and long
message, and the 100 checkpoints of each Monte Carlo test, computed by the procedure of SHAVS
§6.4.  The specifications `SHS.SHA256` and `SHS.SHA512` of `Library.Hashing.Sha2.Spec` hash every
short and long message as well.  Message bytes are packed eight to a word and followed by a word
of nonzero bytes, which the digest must ignore.  The check exits with an error at the first
difference.  Run with `lake env lean --run`; `--only SHA256,SHA224` selects functions by the
names of their files, `--no-spec` skips the specifications, and `--no-monte` skips the Monte Carlo
checkpoints. -/

namespace TestSupport.Hashing.Sha2Vectors

open Library.Hashing.Words

def hexDigit (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else c.toLower.toNat - 'a'.toNat + 10

def bytesOfHex (s : String) : List UInt8 :=
  let cs := s.toList.toArray
  (List.range (cs.size / 2)).map fun i =>
    UInt8.ofNat (16 * hexDigit cs[2 * i]! + hexDigit cs[2 * i + 1]!)

def hexOfBytes (bs : List UInt8) : String :=
  String.join (bs.map fun b =>
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s)

/-- `bytes` packed eight to a word in little-endian order, followed by bytes `0xA5` to the end of
the word after the message's last word. -/
def pack (bytes : List UInt8) : Array UInt64 :=
  let a := bytes.toArray
  (List.range ((a.size + 7) / 8 + 1)).toArray.map fun w =>
    (List.range 8).foldl (fun acc j =>
      let b := (a[8 * w + j]?.getD 0xA5).toUInt64
      acc ||| (b <<< (8 * j).toUInt64)) 0

/-- The first `k` bytes of words packed eight to a word in little-endian order. -/
def unpack (ws : List UInt64) (k : Nat) : List UInt8 :=
  (List.range k).map fun i => (ws[i / 8]!.toNat / 2 ^ (8 * (i % 8))).toUInt8

/-- Bytes as bits, most significant bit first, as FIPS 180-4 orders a message. -/
def toBits (bytes : List UInt8) : List Bool :=
  bytes.flatMap fun b => (List.range 8).reverse.map b.toNat.testBit

/-- The `k` bytes of `x`, most significant first. -/
def bytesOfNat (k x : Nat) : List UInt8 :=
  (List.range k).map fun i => (x / 2 ^ (8 * (k - 1 - i))).toUInt8

structure Algorithm where
  file : String
  bytes : Nat
  program : Array UInt64 → UInt64 → List UInt64
  spec : List Bool → Option Nat

def algorithms : List Algorithm := [
  { file := "SHA256", bytes := 32,
    program := fun m n => let d := Library.Hashing.Sha256.sha256 m n
      [d.w0, d.w1, d.w2, d.w3],
    spec := fun M => if h : M.length < 2 ^ 64 then some (SHS.SHA256.sha256 M h).toNat else none },
  { file := "SHA224", bytes := 28,
    program := fun m n => let d := Library.Hashing.Sha256.sha224 m n
      [d.w0, d.w1, d.w2, d.w3],
    spec := fun M => if h : M.length < 2 ^ 64 then some (SHS.SHA256.sha224 M h).toNat else none },
  { file := "SHA512", bytes := 64,
    program := fun m n => let d := Library.Hashing.Sha512.sha512 m n
      [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7],
    spec := fun M => if h : M.length < 2 ^ 128 then some (SHS.SHA512.sha512 M h).toNat else none },
  { file := "SHA384", bytes := 48,
    program := fun m n => let d := Library.Hashing.Sha512.sha384 m n
      [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5],
    spec := fun M => if h : M.length < 2 ^ 128 then some (SHS.SHA512.sha384 M h).toNat else none },
  { file := "SHA512_256", bytes := 32,
    program := fun m n => let d := Library.Hashing.Sha512.sha512_256 m n
      [d.w0, d.w1, d.w2, d.w3],
    spec := fun M => if h : M.length < 2 ^ 128 then some (SHS.SHA512.sha512_256 M h).toNat
      else none },
  { file := "SHA512_224", bytes := 28,
    program := fun m n => let d := Library.Hashing.Sha512.sha512_224 m n
      [d.w0, d.w1, d.w2, d.w3],
    spec := fun M => if h : M.length < 2 ^ 128 then some (SHS.SHA512.sha512_224 M h).toNat
      else none }]

/-- The digest of `bytes` by the program, as bytes, after checking that the bytes of the last word
after the digest are zero. -/
def digest (a : Algorithm) (bytes : List UInt8) : IO (List UInt8) := do
  let ws := a.program (pack bytes) bytes.length.toUInt64
  let all := unpack ws (8 * ws.length)
  if all.drop a.bytes |>.any (· != 0) then
    throw <| IO.userError s!"{a.file}: nonzero bytes after the digest"
  return all.take a.bytes

def field (line key : String) : Option String :=
  if line.startsWith (key ++ " = ") then some (line.drop (key.length + 3)).toString else none

def lines (path : String) : IO (List String) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").map fun l => (l.replace "\r" "").trimAscii.toString

/-- The short and long messages of one response file: each `Len`, `Msg`, and `MD` triple. -/
def messages (a : Algorithm) (kind : String) (withSpec : Bool) : IO Nat := do
  let path := s!"data/hashing/sha2/{a.file}{kind}.rsp"
  let mut len : Option Nat := none
  let mut msg : List UInt8 := []
  let mut count := 0
  for line in ← lines path do
    if let some v := field line "Len" then len := v.toNat?
    else if let some v := field line "Msg" then msg := bytesOfHex v
    else if let some v := field line "MD" then
      let some bits := len | throw <| IO.userError s!"{path}: MD without Len"
      let bytes := msg.take (bits / 8)
      let want := bytesOfHex v
      let got ← digest a bytes
      if got != want then
        throw <| IO.userError s!"{path}: program, Len {bits}: {hexOfBytes got} ≠ {v}"
      if withSpec then
        match a.spec (toBits bytes) with
        | some x =>
          if bytesOfNat a.bytes x != want then
            throw <| IO.userError s!"{path}: specification, Len {bits}"
        | none => throw <| IO.userError s!"{path}: message too long for the specification"
      count := count + 1
  return count

/-- The Monte Carlo checkpoints of SHAVS §6.4. -/
def monte (a : Algorithm) : IO Nat := do
  let path := s!"data/hashing/sha2/{a.file}Monte.rsp"
  let mut seed : List UInt8 := []
  let mut count := 0
  for line in ← lines path do
    if let some v := field line "Seed" then seed := bytesOfHex v
    else if let some v := field line "MD" then
      let mut md := #[seed, seed, seed]
      for _ in [3:1003] do
        let next ← digest a (md[0]! ++ md[1]! ++ md[2]!)
        md := #[md[1]!, md[2]!, next]
      seed := md[2]!
      if seed != bytesOfHex v then
        throw <| IO.userError s!"{path}: checkpoint {count}: {hexOfBytes seed} ≠ {v}"
      count := count + 1
  return count

def main (args : List String) : IO Unit := do
  let withSpec := !args.contains "--no-spec"
  let withMonte := !args.contains "--no-monte"
  let only := match args.dropWhile (· != "--only") with
    | _ :: names :: _ => some (names.splitOn ",")
    | _ => none
  for a in algorithms.filter fun a => only.all (·.contains a.file) do
    let short ← messages a "ShortMsg" withSpec
    let long ← messages a "LongMsg" withSpec
    let checkpoints ← if withMonte then monte a else pure 0
    IO.println s!"{a.file}: {short} short, {long} long, {checkpoints} Monte Carlo checkpoints"

end TestSupport.Hashing.Sha2Vectors

def main (args : List String) : IO Unit := TestSupport.Hashing.Sha2Vectors.main args
