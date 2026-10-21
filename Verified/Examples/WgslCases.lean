import Verified.Examples.Wgsl

namespace Verified.Examples.WgslCases

private def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)

private def fwords (xs : Array Float32) : Array UInt64 := xs.map fun x => x.toBits.toUInt64

private def gpuArg (arg : LeanExe.WGSL.Arg) : String :=
  s!"u32:{",".intercalate (arg.buffer.toList.map toString)}"

private def wasmArg : LeanExe.WGSL.Arg → String
  | .word value => s!"i64:{value}"
  | .float bits => s!"f32:{bits}"
  | .array xs => s!"array-u64:{words xs.toList}"

private def caseLine (name : String) (n extra : Nat) (inputs : List LeanExe.WGSL.Arg)
    (result : Array UInt64) : String :=
  let groups := max ((n + 63) / 64 + extra) 1
  let initial := n.toUInt64 :: List.replicate n 0x7fc000017fc00001
  let output := (result.size.toUInt64 :: result.toList).flatMap fun (x : UInt64) =>
    [x &&& 0xffffffff, x >>> 32]
  s!"{name}|{groups}|u64:{words initial}|{" ".intercalate (inputs.map gpuArg)}|{words output}"

private def emit (gpu : Bool) (entry kernel : String) (n extra : Nat)
    (inputs : List LeanExe.WGSL.Arg) (result : Array UInt64) : IO Unit :=
  if gpu then IO.println (caseLine kernel n extra inputs result)
  else IO.println s!"wgsl|{entry}|array-u64|{" ".intercalate (inputs.map wasmArg)}|{result.toList}|2|2"

private def floatSpecials : Array Float32 :=
  #[0, 0x80000000, 0x3f800000, 0xc0000000, 1, 0x007fffff, 0x7f800000, 0xff800000, 0x7fc00000,
    0x3f000000, 0xbf000000, 0x3fc00000, 0xbfc00000, 0x40200000, 0xc0200000].map
    Float32.ofBits

def runCases (gpu : Bool := true) : IO Unit := do
  for n in [0, 1, 2, 7, 63, 64, 65] do
    let xs := (List.range n).toArray.map fun i => floatSpecials[i % floatSpecials.size]!
    for gain in floatSpecials do
      emit gpu "scale" "verifiedScale" n 1 [.float gain.toBits, .array (fwords xs)]
        (fwords (Wgsl.scale gain xs))
    emit gpu "roundRoot" "verifiedRoots" n 1 [.array (fwords xs)] (fwords (Wgsl.roundRoot xs))
  for n in [0, 1, 2, 7, 64, 65] do
    for limit in [0, 1, 3, 8] do
      for size in [0, n / 2, n] do
        let xs := (List.range size).toArray.map fun i => floatSpecials[i % floatSpecials.size]!
        emit gpu "branchSum" "verifiedBranch" n 1
          [.array (fwords xs), .word n.toUInt64, .word limit.toUInt64]
          (fwords (Wgsl.branchSum xs n.toUInt64 limit.toUInt64))
  for n in [0, 1, 2, 7, 63, 64, 65] do
    for invert in [false, true] do
      for size in [n / 2, n] do
        let xs := (List.range size).toArray.map fun i => i % 3 == 0
        emit gpu "flags" "verifiedFlags" n 1
          [.array (xs.map Verified.boolWord), .word n.toUInt64, .word (Verified.boolWord invert)]
          ((Wgsl.flags xs n.toUInt64 invert).map Verified.boolWord)
  let values : Array UInt64 := #[0, 1, 0xffffffffffffffff, 0x8000000000000000, 0x100000001, 7]
  for n in [0, 1, 2, 7, 63, 64, 65] do
    for size in [0, n / 2, n] do
      let xs := (List.range size).toArray.map fun i => values[i % values.size]!
      emit gpu "wordScan" "verifiedWords" n 1 [.array xs, .word n.toUInt64]
        (Wgsl.wordScan xs n.toUInt64)

end Verified.Examples.WgslCases
