import TestSupport.M7.Windows
import TestSupport.M7.Qemu

/-!
The command `m7-windows` of the window counts of the Cortex-M7 back end's programs, the echoes
`echo-usart3` and `echo-cmsdk` and the gateways `gateway-usart3` and `gateway-cmsdk`.

- `m7-windows frames` prints each program's functions with their frames and sizes.
- `m7-windows image NAME FILE` writes the bytes of program NAME's code to FILE.
- `m7-windows qemu FILE` writes to FILE the image of the echo of `cmsdkTick` for QEMU's
  `mps2-an500` (`tests/TestSupport/M7/Qemu.lean`): the vector table, UART0's initialization, and
  the program, from address 0.
- `m7-windows static NAME` prints the longest path of each function of program NAME.
- `m7-windows run NAME DIR [IN OUT]` runs program NAME in the model and writes to `DIR/NAME.summary`
  the statistics of each kind of window, to `DIR/NAME.KIND.trace` the first window of each kind, to
  `DIR/NAME.KIND.longest` the longest window of the kind `tick`, and to `DIR/NAME.divisions` each
  call of `udivmod64` in a window of that kind, with its path, operands, and loop passes.  An echo
  receives the bytes of `uart_echo.py`'s lockstep message, blocks of its burst lengths 2, 16, 322,
  and 65,536, and the message again, and must answer each with bit 5 flipped.  A gateway receives
  the input records of the file IN, 18 words a line, and must send the output records of the file
  OUT, 6 words a line, each word's bytes the most significant first.

Each command exits with status 1 on a failure.
-/

open TestSupport.M7.Windows

/-- The lockstep message of `tests/baremetal/uart_echo.py`. -/
def message : List UInt8 :=
  "The request protocol's echo answers each byte with bit 5 flipped.\n".toUTF8.toList ++
    (List.range 256).map UInt8.ofNat

/-- `n` bytes of a block, whose values do not change the echo's path. -/
def block (n : Nat) : List UInt8 := (List.range n).map fun i => UInt8.ofNat (37 * i + 11)

def echoInput : Array UInt8 :=
  (message ++ block 2 ++ block 16 ++ block message.length ++ block 65536 ++ message).toArray

/-- The words of each line of the file at `path`, which must have `k` each. -/
def readRecords (path : String) (k : Nat) : IO (List (List UInt64)) := do
  let lines ← IO.FS.lines path
  lines.toList.mapM fun line => do
    let ws := (line.splitOn " ").filter (· ≠ "")
    match ws.mapM (·.toNat?) with
    | some xs =>
        if xs.length = k then pure (xs.map UInt64.ofNat)
        else throw <| IO.userError s!"{path}: {xs.length} words, not {k}: {line}"
    | none => throw <| IO.userError s!"{path}: not a record of words: {line}"

/-- Runs `act` on the program named `name`. -/
def withProg (name : String) (act : Prog → IO UInt32) : IO UInt32 :=
  match programs.find? (·.name = name) with
  | some p => act p
  | none => do
      IO.eprintln s!"m7-windows: no program {name}"
      return 1

def statLine (kind : String) (s : Stat) : String :=
  s!"{kind} windows {s.count} least {s.least} most {s.most} total {s.total} " ++
    s!"divisions fast {s.divFast} low {s.divLow} loop {s.divLoop} passes {s.divLoopPasses}"

def main (args : List String) : IO UInt32 := do
  match args with
  | ["frames"] =>
      for p in programs do
        match frames p with
        | .ok ls =>
            IO.println s!"{p.name}:"
            for l in ls do IO.println s!"  {l}"
        | .error e =>
            IO.eprintln s!"m7-windows: {p.name}: {e}"
            return 1
      return 0
  | ["image", name, file] => withProg name fun p => do
      match generate p with
      | .ok is =>
          let bytes := LeanExe.M7.imageBytes is
          IO.FS.writeBinFile file (ByteArray.mk bytes.toArray)
          IO.println s!"m7-windows: {name}: {bytes.length} bytes, {is.length} instructions"
          return 0
      | .error e =>
          IO.eprintln s!"m7-windows: {name}: {e}"
          return 1
  | ["qemu", file] =>
      match TestSupport.M7.Qemu.echoImage with
      | .ok bytes =>
          IO.FS.writeBinFile file (ByteArray.mk bytes.toArray)
          IO.println s!"m7-windows: echo-cmsdk-qemu: {bytes.length} bytes"
          return 0
      | .error e =>
          IO.eprintln s!"m7-windows: echo-cmsdk-qemu: {e}"
          return 1
  | ["static", name] => withProg name fun p => do
      match longest p with
      | .ok (ls, l, d) =>
          for line in ls do IO.println line
          IO.println s!"{name}: the step's longest path {l} instructions with {d} divisions"
          return 0
      | .error e =>
          IO.eprintln s!"m7-windows: {name}: {e}"
          return 1
  | "run" :: name :: dir :: rest => withProg name fun p => do
      let (input, expected) ← match rest with
        | [] => pure (echoInput, echoInput.map (· ^^^ 0x20))
        | [inPath, outPath] =>
            let ins ← readRecords inPath 18
            let outs ← readRecords outPath 6
            pure ((ins.flatMap fun r => r.flatMap beBytes).toArray,
              (outs.flatMap fun r => r.flatMap beBytes).toArray)
        | _ => throw <| IO.userError "usage: m7-windows run NAME DIR [IN OUT]"
      let t0 ← IO.monoMsNow
      let r ← runProgram p input expected 100000000 ["tick"]
      let t1 ← IO.monoMsNow
      IO.FS.createDirAll dir
      let kinds := r.stats.toList.map (·.1) |>.toArray.qsort (· < ·)
      let lines := kinds.toList.map fun k => statLine k (r.stats.getD k {})
      let head := s!"{name}: {r.windows} windows, {r.steps} instructions, " ++
        s!"{input.size} bytes in, " ++
        s!"{r.output.size} bytes out, {t1 - t0} ms"
      IO.FS.writeFile s!"{dir}/{name}.summary" (String.join ((head :: lines).map (· ++ "\n")))
      for (k, t) in r.traces.toList do
        IO.FS.writeFile s!"{dir}/{name}.{k}.trace" (String.join (t.toList.map (· ++ "\n")))
      IO.FS.writeFile s!"{dir}/{name}.divisions"
        (String.join (r.divisions.toList.map (· ++ "\n")))
      for (k, t) in r.longest.toList do
        IO.FS.writeFile s!"{dir}/{name}.{k}.longest" (String.join (t.toList.map (· ++ "\n")))
      IO.println head
      for l in lines do IO.println s!"  {l}"
      match r.failure with
      | some e =>
          IO.eprintln s!"m7-windows: {name}: {e}"
          return 1
      | none => return 0
  | _ =>
      IO.eprintln ("usage: m7-windows frames | image NAME FILE | qemu FILE | static NAME | " ++
        "run NAME DIR [IN OUT]")
      return 2
