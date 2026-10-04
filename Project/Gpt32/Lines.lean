import Project.Gpt32.Program

/-!
`gpt32-lines NH F CHUNK VOCAB LAYERS` prints the host commands of `Project/Gpt32/Program.lean`
for the shape `shapeOf NH F CHUNK VOCAB LAYERS`, for the GPT-2 page that `tests/web/serve.py`
serves.  It reads requests from standard input, one per line, and answers each with the command lines
followed by a line `end`: `setup DIR` gives a `shader` command for each kernel, with its text at
`wgsl/NAME.wgsl`, and the lines of `setupItems` with the weights of `DIR`, and `step TOKEN P` gives
the lines of `stepItems` for `TOKEN` at position `P`.  These are the commands of
`Project.Gpt32.generate_host`.  It imports only the program and the binary32 model, so it builds
as a small native executable.
-/

namespace Project.Gpt32

open LeanExe.Examples.Gpt32

/-- The shape with `nh` heads, an MLP of width `f`, `layers` layers, and a vocabulary of `vocab`
tokens in chunks of `chunk` rows, as `Project/Gpt32/Driver.lean` builds it. -/
def linesShape (nh f chunk vocab layers : Nat) : Shape32 :=
  { nh := UInt64.ofNat nh, f := UInt64.ofNat f, chunk := UInt64.ofNat chunk, layers,
    rows := (List.range ((vocab + chunk - 1) / chunk)).map fun c =>
      UInt64.ofNat (min chunk (vocab - c * chunk)) }

def answer (s : Shape32) (request : String) : Except String (List String) :=
  match request.splitOn " " with
  | ["setup", dir] =>
    .ok (KernelName.all.map (fun k => s!"shader {k.shader} wgsl/{k.name}.wgsl") ++
      Item.lines (setupItems s dir))
  | ["step", token, p] =>
    match token.toNat?, p.toNat? with
    | some t, some q => .ok (Item.lines (stepItems s (UInt64.ofNat t) (UInt64.ofNat q)))
    | _, _ => .error s!"bad request: {request}"
  | _ => .error s!"bad request: {request}"

end Project.Gpt32

open Project.Gpt32

def main (args : List String) : IO UInt32 := do
  match args.mapM String.toNat? with
  | some [nh, f, chunk, vocab, layers] =>
    let s := linesShape nh f chunk vocab layers
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      match answer s line.trimAscii.toString with
      | .ok lines =>
        for l in lines do stdout.putStrLn l
        stdout.putStrLn "end"
      | .error e => stdout.putStrLn s!"error {e}"
      stdout.flush
    return 0
  | _ =>
    IO.eprintln "usage: gpt32-lines NH F CHUNK VOCAB LAYERS"
    return 2
