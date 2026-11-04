import Demos.Gpt32.VerifiedKernels
import Demos.Gpt32.VerifiedPtxKernels
import LeanExe.WGSL.Parse
import LeanExe.PTX.Parse

/-!
Runs the programs of `Demos/Gpt32/HostProgram.lean` on a host session: `leanexe-webgpu-host
session` with the WGSL kernels of `Demos.Gpt32.Verified.kernelMap`, or `leanexe-cuda-host session`
with the PTX kernels of `Demos.Gpt32.VerifiedPtx.kernelMap`.  The driver writes the text of each
kernel, which for PTX `ptxas -O3 --fmad=false` compiles for the GPU that `leanexe-cuda-host info`
reports, starts the host, sends the lines that load the kernels and then the lines of `setupItems`
and of `stepItems` for each position, which are the commands of `Demos.Gpt32.generate_host`, and
reads the scores after each step from the last prompt position on.  It chooses each token with
`greedy32`.
-/

namespace Demos.Gpt32

open Demos.Gpt32 LeanExe.WGSL

/-- The WGSL text of kernel `k`, after checking that the parser reads it back as the kernel, as
`tools/EmitWgsl.lean` does. -/
def wgslText (k : KernelName) : Except String String :=
  let text := (Verified.kernelMap k).print
  match Module.parse text with
  | some parsed =>
    if toString (repr parsed) == toString (repr (Verified.kernelMap k)) then .ok text
    else .error s!"{k.name}: the text parses to a different kernel"
  | none => .error s!"{k.name}: the text does not parse"

/-- The shape with `nh` heads, an MLP of width `f`, `layers` layers, and a vocabulary of `vocab`
tokens in chunks of `chunk` rows. -/
def shapeOf (nh f chunk vocab layers : Nat) : Shape32 :=
  { nh := UInt64.ofNat nh, f := UInt64.ofNat f, chunk := UInt64.ofNat chunk, layers,
    rows := (List.range ((vocab + chunk - 1) / chunk)).map fun c =>
      UInt64.ofNat (min chunk (vocab - c * chunk)) }

/-- The PTX text of kernel `k`, after checking that the parser reads it back as the kernel, as
`tools/EmitPtx.lean` does. -/
def ptxText (k : KernelName) : Except String String :=
  let text := (VerifiedPtx.kernelMap k).print
  match LeanExe.PTX.Module.parse text with
  | some parsed =>
    if toString (repr parsed) == toString (repr (VerifiedPtx.kernelMap k)) then .ok text
    else .error s!"{k.name}: the text parses to a different kernel"
  | none => .error s!"{k.name}: the text does not parse"

/-- The kernels of a host: WGSL for `leanexe-webgpu-host`, PTX for `leanexe-cuda-host`. -/
inductive Target where
  | wgsl
  | ptx

def Target.ofString? : String → Option Target
  | "wgsl" => some .wgsl
  | "ptx" => some .ptx
  | _ => none

def runTool (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode != 0 then
    throw <| IO.userError s!"{cmd} failed: {out.stderr}"
  return out.stdout

/-- The architecture `sm_XY` of the GPU whose compute capability `host info` reports. -/
def cudaArch (host : String) : IO String := do
  let info ← runTool host #["info"]
  let found := (info.splitOn "\n").findSome? fun line =>
    match line.splitOn "compute capability " with
    | ["", version] =>
      match version.splitOn "." with
      | [major, minor] => some s!"sm_{major}{minor}"
      | _ => none
    | _ => none
  match found with
  | some arch => return arch
  | none => throw <| IO.userError s!"{host} info reports no compute capability"

/-- Writes the kernels of `target` to `dir` and returns the session lines that load them.  For
PTX it also writes the version of `ptxas` to `ptxas.version`. -/
def kernelLines (target : Target) (host dir : String) : IO (List String) := do
  IO.FS.createDirAll dir
  match target with
  | .wgsl =>
    KernelName.all.mapM fun k => do
      let path := s!"{dir}/{k.name}.wgsl"
      IO.FS.writeFile path (← IO.ofExcept (wgslText k))
      return s!"shader {k.shader} {path}"
  | .ptx =>
    let arch ← cudaArch host
    let ptxas := s!"{(← IO.getEnv "CUDA_HOME").getD "/usr/local/cuda"}/bin/ptxas"
    IO.FS.writeFile s!"{dir}/ptxas.version" (← runTool ptxas #["--version"])
    KernelName.all.mapM fun k => do
      let path := s!"{dir}/{k.name}.ptx"
      let cubin := s!"{dir}/{k.name}.cubin"
      IO.FS.writeFile path (← IO.ofExcept (ptxText k))
      discard <| runTool ptxas #[s!"-arch={arch}", "-O3", "--fmad=false", path, "-o", cubin]
      return s!"kernel {k.shader} {cubin}"

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

/-- Generates `n` tokens after `prompt` on the session of `host` with the kernels of `target`,
which it writes to `kernels`, calling `seen` with the scores of each step from the last prompt
position on, and returns the prompt followed by the generated tokens. -/
def generate (target : Target) (host weights kernels tmp : String) (s : Shape32)
    (prompt : List Nat) (n : Nat) (seen : List (Array Float32) → IO Unit) : IO (List Nat) := do
  let lines ← kernelLines target host kernels
  let h ← startHost host
  lines.forM (send h)
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

end Demos.Gpt32
