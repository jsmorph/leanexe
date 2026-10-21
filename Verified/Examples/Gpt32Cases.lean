import Examples.Gpt32.Program
import LeanExe.WGSL.Build

namespace Verified.Examples.Gpt32Cases

open _root_.Examples.Gpt32 LeanExe.WGSL

private def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)
private def fwords (xs : Array Float32) : Array UInt64 := xs.map fun x => x.toBits.toUInt64
private def arr (xs : Array Float32) : Arg := .array (fwords xs)

private def gpuArg (arg : Arg) : String :=
  s!"u32:{",".intercalate (arg.buffer.toList.map toString)}"

private def wasmArg : Arg → String
  | .word value => s!"i64:{value}"
  | .float bits => s!"f32:{bits}"
  | .array xs => s!"array-u64:{words xs.toList}"

private def emit (gpu : Bool) (kernel entry : String) (inputs : List Arg)
    (result : Array Float32) : IO Unit := do
  let encoded := fwords result
  if gpu then
    let n := result.size
    let groups := max ((n + 63) / 64 + 1) 1
    let initial := n.toUInt64 :: List.replicate n 0x7fc000017fc00001
    let output := (n.toUInt64 :: encoded.toList).flatMap fun (x : UInt64) =>
      [x &&& 0xffffffff, x >>> 32]
    IO.println s!"{kernel}|{groups}|u64:{words initial}|{" ".intercalate (inputs.map gpuArg)}|{words output}"
  else
    let blocks := 1 + (inputs.filter fun a => match a with | .array _ => true | _ => false).length
    IO.println s!"gpt32|{entry}|array-u64|{" ".intercalate (inputs.map wasmArg)}|{encoded.toList}|{blocks}|{blocks}"

private def specials : Array Float32 :=
  #[0, 0x80000000, 0x3f800000, 0xbf800000, 1, 0x007fffff, 0x7f800000, 0xff800000,
    0x7fc00000, 0x3f000000, 0xbf000000, 0x3fc00000, 0xbfc00000].map Float32.ofBits

private def values (n seed : Nat) : Array Float32 :=
  Array.ofFn (n := n) fun i =>
    if (i.val + seed) % 11 = 0 then specials[(i.val / 11 + seed) % specials.size]!
    else (((i.val * 37 + seed * 101) % 401).toFloat / 100.0 - 2.0).toFloat32

def runCases (gpu : Bool := false) : IO Unit := do
  for n in [0, 1, 2, 7, 63, 64, 65, 1000] do
    let x := Array.ofFn (n := n) fun i => specials[i.val % specials.size]!
    emit gpu "exp" "expArray32" [arr x] (expArray32 x)
    emit gpu "gelu" "geluArray32" [arr x] (geluArray32 x)
  for d in [0, 1, 8, 64] do
    for short in [false, true] do
      let size := if short then d / 2 else d
      let x := values size 2
      let g := values d 3
      let b := values size 4
      let wte := values (3 * size) 5
      let wpe := values (4 * size) 6
      for row in [0, 2, 4] do
        emit gpu "embed" "embed32" [arr wte, arr wpe, .word row, .word 3, .word d.toUInt64]
          (embed32 wte wpe row 3 d.toUInt64)
      emit gpu "layerNorm" "layerNorm32"
        [arr x, arr g, arr b, .word d.toUInt64, .float d.toFloat.toFloat32.toBits]
        (layerNorm32 x g b d.toUInt64 d.toFloat.toFloat32)
      emit gpu "add" "add32" [arr g, arr x] (add32 g x)
      emit gpu "append" "append32" [arr x, arr b, .word d.toUInt64, .word (d + 2).toUInt64]
        (append32 x b d.toUInt64 (d + 2).toUInt64)
      for k in [0, 1, 7] do
        for m in [0, 1, d + 1] do
          let a := values (if short then k / 2 else k) 7
          let w := values (if short then k * m / 2 else k * m) 8
          let bias := values (if short then m / 2 else m) 9
          emit gpu "linear" "linear32" [arr a, arr w, arr bias, .word k.toUInt64, .word m.toUInt64]
            (linear32 a w bias k.toUInt64 m.toUInt64)
      for rows in [0, 1, 3] do
        emit gpu "logits" "logits32" [arr x, arr wte, .word rows, .word d.toUInt64]
          (logits32 x wte rows d.toUInt64)
  for nh in [0, 1, 2] do
    for p in [0, 2] do
      for short in [false, true] do
        let d := 64 * nh
        let size := if short then d / 2 else d
        let q := values size 10
        let kc := values ((p + 1) * size) 11
        let vc := values ((p + 1) * size) 12
        let n := nh * 1024
        let sc := scores32 q kc p.toUInt64 d.toUInt64 n.toUInt64
        emit gpu "scores" "scores32" [arr q, arr kc, .word p.toUInt64, .word d.toUInt64,
          .word n.toUInt64] sc
        let mx := headMax32 sc p.toUInt64 nh.toUInt64
        emit gpu "headMax" "headMax32" [arr sc, .word p.toUInt64, .word nh.toUInt64] mx
        let sm := headSum32 sc mx p.toUInt64 nh.toUInt64
        emit gpu "headSum" "headSum32" [arr sc, arr mx, .word p.toUInt64, .word nh.toUInt64] sm
        let pw := probs32 sc mx sm p.toUInt64 n.toUInt64
        emit gpu "probs" "probs32" [arr sc, arr mx, arr sm, .word p.toUInt64, .word n.toUInt64] pw
        emit gpu "mix" "mix32" [arr pw, arr vc, .word p.toUInt64, .word d.toUInt64]
          (mix32 pw vc p.toUInt64 d.toUInt64)

end Verified.Examples.Gpt32Cases
