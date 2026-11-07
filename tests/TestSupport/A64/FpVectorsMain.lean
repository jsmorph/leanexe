import TestSupport.A64.FpVectors

/-!
The command `a64-fpvectors` of the test of the floating-point forms' meanings
(`tests/baremetal/a64-fpvectors.sh`).  `a64-fpvectors gen SEED COUNT DIR` writes DIR/fp.img, the
arm64 Image of COUNT vectors of each form from the seed SEED, and DIR/fp.layout, whose first line
gives the offset of the vectors' words in the Image and whose other lines give each block's form,
class, and number of vectors.  `a64-fpvectors check DIR SERIAL` compares the result words of the
UART output SERIAL with the model for the vectors of DIR/fp.img.  For each block and each form it
prints the numbers of vectors, of disagreements, and of each of the form's tags of `tagsOf`, and
then every disagreement with its operands, and it exits with status 1 when a result differs or the
output cannot be checked.
-/

open TestSupport.A64 TestSupport.A64.Fp

def hex16 (w : UInt64) : String :=
  let s := String.ofList (Nat.toDigits 16 w.toNat)
  "0x" ++ String.ofList (List.replicate (16 - s.length) '0') ++ s

def parseLayout (text : String) : Except String (Nat × List Block) := do
  let lines := (text.splitOn "\n").filter (· ≠ "")
  let off ← match lines.head?.map (·.splitOn " ") with
    | some ["data", o] =>
        match o.toNat? with
        | some v => pure v
        | none => throw "the data line's offset is not a number"
    | _ => throw "the layout does not start with its data line"
  let blocks ← lines.tail.mapM fun l =>
    match l.splitOn " " with
    | [f, c, n] =>
        match Form.ofName f, n.toNat? with
        | some form, some count => pure { form, cls := c, count }
        | _, _ => throw s!"the layout line {l}"
    | _ => throw s!"the layout line {l}"
  return (off, blocks)

def main (args : List String) : IO UInt32 := do
  match args with
  | ["gen", seed, count, dir] =>
      match seed.toNat?, count.toNat? with
      | some s, some n =>
          let (data, blocks) := vectors (UInt64.ofNat s) n
          let counts := Form.all.map fun f =>
            (f, blocks.foldl (fun k b => if b.form == f then k + b.count else k) 0)
          match image data counts with
          | .error e =>
              IO.println s!"fail: the image: {e}"
              return 1
          | .ok (img, off) =>
              IO.FS.writeBinFile s!"{dir}/fp.img" img
              IO.FS.writeFile s!"{dir}/fp.layout" <| String.join <|
                s!"data {off}\n" :: blocks.map fun b => s!"{b.form.name} {b.cls} {b.count}\n"
              IO.println s!"a64-fpvectors: {n} vectors of each form from seed {s}, an Image of {img.size} bytes"
              return 0
      | _, _ =>
          IO.eprintln "a64-fpvectors: SEED and COUNT must be natural numbers"
          return 2
  | ["check", dir, serial] =>
      let img ← IO.FS.readBinFile s!"{dir}/fp.img"
      let out ← IO.FS.readBinFile serial
      let layout ← IO.FS.readFile s!"{dir}/fp.layout"
      match parseLayout layout >>= fun (off, blocks) => checkRun img out off blocks with
      | .error e =>
          IO.println s!"fail: {e}"
          return 1
      | .ok (outcomes, diffs) =>
          let tagText (f : Form) (ts : Array Nat) :=
            ", ".intercalate (f.tags.map fun t => s!"{t.name} {ts[t.index]!}")
          for o in outcomes do
            IO.println s!"block {o.block.form.name} {o.block.cls}: {o.block.count} vectors, {o.bad} differ; {tagText o.block.form o.tags}"
          for f in Form.all do
            let mine := outcomes.filter (·.block.form == f)
            let sum := mine.foldl (fun acc o => acc.zipWith (· + ·) o.tags)
              (Tag.all.toArray.map fun _ => 0)
            let n := mine.foldl (fun k o => k + o.block.count) 0
            let bad := mine.foldl (fun k o => k + o.bad) 0
            IO.println s!"form {f.name}: {n} vectors, {bad} differ; {tagText f sum}"
          for d in diffs do
            IO.println s!"differ: {d.form.name} {d.cls} {hex16 d.a} {hex16 d.b}: {hex16 d.got}, model {hex16 d.want}"
          let total := outcomes.foldl (fun n o => n + o.block.count) 0
          IO.println s!"a64-fpvectors: {total - diffs.size} of {total} results agree with the model"
          return if diffs.isEmpty then 0 else 1
  | _ =>
      IO.eprintln "usage: a64-fpvectors gen SEED COUNT DIR | a64-fpvectors check DIR SERIAL"
      return 2
