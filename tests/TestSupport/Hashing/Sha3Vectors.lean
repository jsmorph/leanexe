import Library.Hashing.Sha3.Spec
import Library.Hashing.Sha3.Program
import TestSupport.Hashing.Packing

/-! A check of the FIPS 202 transcription `Library.Hashing.Sha3.Spec` and the programs of
`Library.Hashing.Sha3` on the NIST CAVP vectors in `data/hashing/sha3/`.  The transcription runs
the short and long messages of SHA3-224, SHA3-256, SHA3-384, SHA3-512, SHAKE128, and SHAKE256,
the variable outputs of the two SHAKE functions, and the bit-oriented short messages in `bit/`.
The programs run the same byte-oriented files and the 100 checkpoints of each Monte Carlo test,
computed by the procedures of SHA3VS §6.2.3 and §6.3.3.  A message of `Len` bits is
`h2b(Msg, Len)` of Appendix B.1 for the transcription and the bytes of `Msg` packed eight to a word
for a program, followed by a word of nonzero bytes, which the result must ignore.  A program's
digest must have zero bytes after its length, and its SHAKE output `⌈d / 8⌉` words.  The check
exits with an error at the first difference.  Run the executable `sha3-vectors`; `--only
SHA3_256,SHAKE128` selects functions by the names of their files, `--kinds ShortMsg,bit` selects
among `ShortMsg`, `LongMsg`, `VariableOut`, `Monte`, and `bit`, `--no-spec` skips the
transcription, and `--no-program` skips the programs. -/

namespace TestSupport.Hashing.Sha3Vectors

open Library.Hashing.Sha3.Spec TestSupport.Hashing.Packing

/-- A function of the files.  `bytes` is the digest length of a hash function and none for an
XOF, `spec` takes the output length in bits, and `program` takes the message words, the message
length in bytes, and the output length in bytes. -/
structure Function where
  file : String
  bytes : Option Nat
  spec : Bits → Nat → Bits
  program : Array UInt64 → UInt64 → UInt64 → List UInt64

def words4 (d : Library.Hashing.Words.Words4) : List UInt64 := [d.w0, d.w1, d.w2, d.w3]

def functions : List Function := [
  { file := "SHA3_224", bytes := some 28, spec := fun M _ => sha3_224 M,
    program := fun m n _ => words4 (Library.Hashing.Sha3.sha3_224 m n) },
  { file := "SHA3_256", bytes := some 32, spec := fun M _ => sha3_256 M,
    program := fun m n _ => words4 (Library.Hashing.Sha3.sha3_256 m n) },
  { file := "SHA3_384", bytes := some 48, spec := fun M _ => sha3_384 M,
    program := fun m n _ =>
      let d := Library.Hashing.Sha3.sha3_384 m n
      [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5] },
  { file := "SHA3_512", bytes := some 64, spec := fun M _ => sha3_512 M,
    program := fun m n _ =>
      let d := Library.Hashing.Sha3.sha3_512 m n
      [d.w0, d.w1, d.w2, d.w3, d.w4, d.w5, d.w6, d.w7] },
  { file := "SHAKE128", bytes := none, spec := shake128,
    program := fun m n d => (Library.Hashing.Sha3.shake128 m n d).toList },
  { file := "SHAKE256", bytes := none, spec := shake256,
    program := fun m n d => (Library.Hashing.Sha3.shake256 m n d).toList }]

/-- The program's result for `msg` as `k` bytes, after checking its words past the result. -/
def run (fn : Function) (msg : List UInt8) (k : Nat) : IO (List UInt8) := do
  let ws := fn.program (pack msg) msg.length.toUInt64 k.toUInt64
  if fn.bytes.isNone && ws.length != (k + 7) / 8 then
    throw <| IO.userError s!"{fn.file}: {ws.length} output words for {k} bytes"
  let all := unpack ws (8 * ws.length)
  if all.drop k |>.any (· != 0) then
    throw <| IO.userError s!"{fn.file}: nonzero bytes after the result"
  return all.take k

def field (line key : String) : Option String :=
  if line.startsWith (key ++ " = ") then some (line.drop (key.length + 3)).toString else none

/-- The value of a header line `[key = value]`. -/
def header (line key : String) : Option String :=
  if line.startsWith "[" && line.endsWith "]" then
    field (String.ofList (line.toList.drop 1).dropLast) key
  else none

def lines (path : String) : IO (List String) := do
  let text ← IO.FS.readFile path
  return (text.splitOn "\n").map fun l => (l.replace "\r" "").trimAscii.toString

/-- The vectors of one response file: each message with its expected digest or output, checked as
they are read.  The output length of an XOF is the file's `Outputlen` header, or each vector's
`Outputlen` in a variable-output file. -/
def check (fn : Function) (path : String) (spec program : Bool) : IO Nat := do
  let mut len : Option Nat := none
  let mut msg : Option String := none
  let mut outLen : Option Nat := none
  let mut count := 0
  for line in ← lines path do
    if let some v := header line "Outputlen" then outLen := v.toNat?
    else if let some v := field line "Outputlen" then outLen := v.toNat?
    else if let some v := field line "Len" then len := v.toNat?
    else if let some v := field line "Msg" then msg := some v
    else if let some want := (field line "MD").orElse fun _ => field line "Output" then
      let some m := msg | throw <| IO.userError s!"{path}: a digest without Msg"
      let n := len.getD (4 * m.length)
      let d ← match fn.bytes, outLen with
        | some b, _ => pure (8 * b)
        | none, some d => pure d
        | none, none => throw <| IO.userError s!"{path}: an output without Outputlen"
      if spec then
        let got := b2h (fn.spec (h2b m n) d)
        unless got.toLower == want.toLower do
          throw <| IO.userError s!"{path}: Len {n} Msg {m}: transcription {got.toLower}"
      if program && n % 8 == 0 && d % 8 == 0 then
        let got := hexOfBytes (← run fn ((bytesOfHex m).take (n / 8)) (d / 8))
        unless got == want.toLower do
          throw <| IO.userError s!"{path}: Len {n} Msg {m}: program {got}"
      count := count + 1
      len := none
      msg := none
  return count

/-- The Monte Carlo checkpoints of a hash function, SHA3VS §6.2.3: each digest is the next
message, and every thousandth of the 100,000 digests is a checkpoint. -/
def monteHash (fn : Function) (bytes : Nat) (path : String) : IO Nat := do
  let mut md : List UInt8 := []
  let mut count := 0
  for line in ← lines path do
    if let some v := field line "Seed" then md := bytesOfHex v
    else if let some want := field line "MD" then
      for _ in [0:1000] do md ← run fn md bytes
      unless hexOfBytes md == want.toLower do
        throw <| IO.userError s!"{path}: checkpoint {count}: {hexOfBytes md}"
      count := count + 1
  return count

/-- The Monte Carlo checkpoints of an XOF, SHA3VS §6.3.3: each message is the first 16 bytes of
the output before it, zero-padded, and the next output length in bytes is `minoutbytes` plus the
output's last two bytes, read as a big-endian integer, modulo the range of lengths. -/
def monteXof (fn : Function) (path : String) : IO Nat := do
  let mut minBytes := 0
  let mut maxBytes := 0
  let mut out : List UInt8 := []
  let mut outLen := 0
  let mut wantLen : Option Nat := none
  let mut count := 0
  for line in ← lines path do
    if let some v := header line "Minimum Output Length (bits)" then
      minBytes := (v.toNat! + 7) / 8
    else if let some v := header line "Maximum Output Length (bits)" then
      maxBytes := v.toNat! / 8
      outLen := maxBytes
    else if let some v := field line "Msg" then out := bytesOfHex v
    else if let some v := field line "Outputlen" then wantLen := v.toNat?
    else if let some want := field line "Output" then
      let mut checkpointLen := outLen
      for i in [1:1001] do
        let m := (out ++ List.replicate 16 0).take 16
        out ← run fn m outLen
        if i == 1000 then checkpointLen := outLen
        let r := out.length
        let rightmost := 256 * (out.getD (r - 2) 0).toNat + (out.getD (r - 1) 0).toNat
        outLen := minBytes + rightmost % (maxBytes - minBytes + 1)
      unless hexOfBytes out == want.toLower && wantLen == some (8 * checkpointLen) do
        throw <| IO.userError s!"{path}: checkpoint {count} of {checkpointLen} bytes"
      count := count + 1
  return count

def option (args : List String) (name : String) : Option (List String) :=
  match args.dropWhile (· != name) with
  | _ :: v :: _ => some (v.splitOn ",")
  | _ => none

def main (args : List String) : IO UInt32 := do
  let only := option args "--only"
  let kinds := (option args "--kinds").getD ["ShortMsg", "LongMsg", "VariableOut", "Monte", "bit"]
  let spec := !args.contains "--no-spec"
  let program := !args.contains "--no-program"
  let mut total := 0
  for fn in functions do
    if only.any (!·.contains fn.file) then continue
    for kind in kinds do
      if kind == "VariableOut" && fn.bytes.isSome then continue
      if kind == "Monte" && !program then continue
      if kind == "bit" && !spec then continue
      let start ← IO.monoMsNow
      let n ← match kind, fn.bytes with
        | "bit", _ => check fn s!"data/hashing/sha3/bit/{fn.file}ShortMsg.rsp" true false
        | "Monte", some b => monteHash fn b s!"data/hashing/sha3/{fn.file}Monte.rsp"
        | "Monte", none => monteXof fn s!"data/hashing/sha3/{fn.file}Monte.rsp"
        | k, _ => check fn s!"data/hashing/sha3/{fn.file}{k}.rsp" spec program
      IO.println s!"{fn.file} {kind}: {n} vectors agree ({(← IO.monoMsNow) - start} ms)"
      (← IO.getStdout).flush
      total := total + n
  IO.println s!"sha3: {total} vectors agree"
  return 0

end TestSupport.Hashing.Sha3Vectors

def main (args : List String) : IO UInt32 := TestSupport.Hashing.Sha3Vectors.main args
