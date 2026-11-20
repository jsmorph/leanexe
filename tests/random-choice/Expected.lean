import Demos.RandomChoice.CommandSpec

/-! The output and the status that the specification gives a run of the unbiased random choice's
command whose `random_get` calls take the bytes of a file in order, as they do in the Wasmtime host
with `--random-bytes FILE`: a call takes the file's next bytes, and a call that asks for more bytes
than remain returns errno 29 (`io`).  Writes take every byte that they offer.

`tests/random-choice/run.sh` runs `lake env lean --run` on this file with a directory and the names
of its cases.  For each name, `NAME.args` holds the arguments, the program name first, one to a
line, and `NAME.bytes` the random bytes.  The script writes the output that the specification gives
to `NAME.expected` and the status in decimal to `NAME.status`.

The run follows `Meets` of `Demos/RandomChoice/CommandSpec.lean`.  When `parseSpec` refuses N or K,
the status is 2 and the run writes nothing.  Otherwise the passes of `Rounds` from K values and
`passes K` passes each draw 4,096 bytes and write `passText` of them.  A draw that returns an errno
ends the run with that errno as the status after the writes of the passes before it, and the passes
end with status 0 when no value remains and with `capStatus` when no pass remains.  The script fails
when a run with status 0 writes other bytes than `renderSpec` of the first K picks of the accepted
words drawn, or draws fewer than K accepted words, and when a run at the cap draws other than
`512 · passes K` words or K accepted words or more, which `Meets` excludes. -/

namespace RandomChoiceExpected

open LeanExe Demos.RandomChoice

/-- The buffer that `args_get` fills for `args`: each argument's UTF-8 bytes followed by a zero
byte. -/
def argBuffer (args : List String) : Bytes :=
  ⟨⟨(args.flatMap fun a => a.toUTF8.toList ++ [0]).toArray⟩⟩

/-- The passes of `Rounds n r p` whose draws take their bytes from `file`: the bytes `drawn`
followed by those that the draws returned, the bytes `written` followed by those that the passes
wrote, and the status. -/
partial def rounds (n r : UInt64) (p : Nat) (file drawn written : List UInt8) :
    List UInt8 × List UInt8 × UInt64 :=
  if r = 0 then (drawn, written, 0)
  else if p = 0 then (drawn, written, capStatus)
  else if file.length < 4096 then (drawn, written, 29)
  else
    let buffer : Bytes := ⟨⟨(file.take 4096).toArray⟩⟩
    rounds n (r - UInt64.ofNat (passPicks n r buffer).length) (p - 1) (file.drop 4096)
      (drawn ++ file.take 4096) (written ++ passText n r buffer)

/-- The output and the status of a run with the arguments `args` and the random bytes `file`. -/
def expected (args : List String) (file : List UInt8) : Except String (List UInt8 × UInt64) := do
  let a := argBuffer args
  let n := parseSpec (a, 1)
  let k := parseSpec (a, 2)
  if n = 0 ∨ k = 0 then return ([], 2)
  let (drawn, written, status) := rounds n k (passes k).toNat file [] []
  let chosen := accepted n (Demos.RandomHistogram.words drawn)
  if status = 0 then
    unless written = (renderSpec (chosen.take k.toNat).toArray).data.data.toList ∧
        k.toNat ≤ chosen.length do
      throw "the output differs from renderSpec of the first K accepted words"
  if status = capStatus then
    unless (Demos.RandomHistogram.words drawn).length = 512 * (passes k).toNat ∧
        chosen.length < k.toNat do
      throw "the words drawn at the cap differ from those that Meets states"
  return (written, status)

end RandomChoiceExpected

open RandomChoiceExpected in
def main (args : List String) : IO UInt32 := do
  let dir :: names@(_ :: _) := args
    | throw (IO.userError "usage: lean --run tests/random-choice/Expected.lean DIR NAME...")
  for name in names do
    let argv ← IO.FS.lines s!"{dir}/{name}.args"
    let file ← IO.FS.readBinFile s!"{dir}/{name}.bytes"
    match expected argv.toList file.toList with
    | .ok (out, status) =>
      IO.FS.writeBinFile s!"{dir}/{name}.expected" ⟨out.toArray⟩
      IO.FS.writeFile s!"{dir}/{name}.status" s!"{status}\n"
    | .error message => throw (IO.userError s!"{name}: {message}")
  return 0
