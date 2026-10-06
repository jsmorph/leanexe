import Examples.Gpt32.Specs
import LeanExe.WGSL.Parse

/-!
Runs the programs of `Examples/Gpt32/HostProgram.lean` on `leanexe-webgpu-host session`.  The driver
writes each kernel's WGSL text, starts the host, sends the shader commands and then the lines of
`setupItems` and of `stepItems` for each position, which are the commands of
`Examples.Gpt32.generate_host`, and reads the scores after each step from the last prompt position
on.  It chooses each token with `greedy32`.
-/

namespace Examples.Gpt32

open Examples.Gpt32 LeanExe.WGSL

/-- The WGSL text of kernel `k`, after checking that the parser reads it back as the kernel, as
`tools/EmitWgsl.lean` does. -/
def kernelText (k : KernelName) : Except String String :=
  let text := k.module.print
  match Module.parse text with
  | some parsed =>
    if toString (repr parsed) == toString (repr k.module) then .ok text
    else .error s!"{k.name}: the text parses to a different kernel"
  | none => .error s!"{k.name}: the text does not parse"

/-- The shape with `nh` heads, an MLP of width `f`, `layers` layers, and a vocabulary of `vocab`
tokens in chunks of `chunk` rows. -/
def shapeOf (nh f chunk vocab layers : Nat) : Shape32 :=
  { nh := UInt64.ofNat nh, f := UInt64.ofNat f, chunk := UInt64.ofNat chunk, layers,
    rows := (List.range ((vocab + chunk - 1) / chunk)).map fun c =>
      UInt64.ofNat (min chunk (vocab - c * chunk)) }

abbrev HostProcess := IO.Process.Child { stdin := .piped, stdout := .piped, stderr := .inherit }

def startHost (host : String) : IO HostProcess :=
  IO.Process.spawn { cmd := host, args := #["session"], stdin := .piped, stdout := .piped,
                     stderr := .inherit }

def send (h : HostProcess) (line : String) : IO Unit := do
  h.stdin.putStrLn line
  h.stdin.flush
  let reply ← h.stdout.getLine
  if reply.trimAscii.toString != "ok" then
    throw <| IO.userError s!"host failed on: {line}"

def sendItems (h : HostProcess) (items : List Item) : IO Unit :=
  (Item.lines items).forM (send h)

def stopHost (h : HostProcess) : IO Unit := do
  h.stdin.putStrLn "quit"
  h.stdin.flush
  let code ← h.wait
  if code != 0 then
    throw <| IO.userError s!"host exited with {code}"

def word32 (b : ByteArray) (o : Nat) : UInt32 :=
  b[o]!.toUInt32 ||| (b[o + 1]!.toUInt32 <<< 8) ||| (b[o + 2]!.toUInt32 <<< 16) |||
    (b[o + 3]!.toUInt32 <<< 24)

/-- The binary32 array whose Wasm array words the bytes `b` hold. -/
def floatsOf (b : ByteArray) : Array Float32 :=
  let n := (b.size - 8) / 8
  Array.ofFn (n := n) fun i => Float32.ofBits (word32 b (8 + 8 * i.val))

/-- The scores of each chunk, read through the file `tmp`. -/
def readScores (h : HostProcess) (s : Shape32) (tmp : String) : IO (List (Array Float32)) :=
  (List.range s.rows.length).mapM fun c => do
    send h s!"read {(Buf.z c).name} {tmp}"
    return floatsOf (← IO.FS.readBinFile tmp)

/-- Generates `n` tokens after `prompt`, calling `seen` with the scores of each step from the last
prompt position on, and returns the prompt followed by the generated tokens. -/
def generate (host weights wgsl tmp : String) (s : Shape32) (prompt : List Nat) (n : Nat)
    (seen : List (Array Float32) → IO Unit) : IO (List Nat) := do
  IO.FS.createDirAll wgsl
  let h ← startHost host
  for k in KernelName.all do
    let path := s!"{wgsl}/{k.name}.wgsl"
    IO.FS.writeFile path (← IO.ofExcept (kernelText k))
    send h s!"shader {k.shader} {path}"
  sendItems h (setupItems s weights)
  let mut ids := prompt.toArray
  for p in [0:prompt.length + n - 1] do
    sendItems h (stepItems s (UInt64.ofNat ids[p]!) (UInt64.ofNat p))
    if p + 1 ≥ prompt.length then
      let scores ← readScores h s tmp
      seen scores
      ids := ids.push (greedy32 scores)
  stopHost h
  return ids.toList

end Examples.Gpt32
