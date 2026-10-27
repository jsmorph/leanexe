import Verified.Examples.TypedTrees
import TestSupport.Host
import TestSupport.Records

/-! The cases of the trees whose records hold typed fields.  The host passes and prints a tree in
the `records-u64` form, which native Lean computes from the `Encode` instance, so each case also
checks the slot words of the `Bool`, binary64, binary32, structure, and enumeration fields.  The
block counts follow the code: a borrowed tree keeps the host's records, a construction allocates
one record, a copy one record for each record of the tree, and `flip`, `scale`, `settle`, `bump`,
and `blacken` reuse the records of their owned argument. -/

namespace Verified.Examples.TypedTrees

open TestSupport.Host LeanExe.Pipeline

def Samples.records : Samples → Nat
  | .empty => 0
  | .sample l _ _ _ _ r => 1 + l.records + r.records
  | .mark _ _ => 1

/-- The depth of the deepest call of a recursion over `t` that recurses into every child, the
root's call at depth 0. -/
def Samples.height : Samples → Nat
  | .empty | .mark _ _ => 0
  | .sample l _ _ _ _ r => 1 + max l.height r.height

/-- A chain of `n` samples down the right, ending in a mark. -/
def Samples.chain : Nat → Samples
  | 0 => .mark true 0.25
  | n + 1 => .sample .empty (n % 2 == 0) (Float.ofNat n) (Float32.ofNat n) (UInt64.ofNat n)
      (Samples.chain n)

/-- A tree of at most `n` constructors and `fuel` levels from the arbitrary words of `seed`. -/
def Samples.arbitraryWith : Nat → Nat → Nat → Samples
  | 0, _, _ | _, 0, _ => .empty
  | fuel + 1, n + 1, seed =>
    let left := (rw (seed + 1)).toNat % (n + 1)
    match (rw seed).toNat % 3 with
    | 0 => .mark ((rw (seed + 3)).toNat % 2 == 0) (rf (seed + 5))
    | 1 => .empty
    | _ => .sample (Samples.arbitraryWith fuel left (2 * seed + 1)) ((rw (seed + 2)).toNat % 2 == 1)
      (rf (seed + 7)) (Float32.ofBits (rw (seed + 9)).toUInt32) (rw (seed + 11))
      (Samples.arbitraryWith fuel (n - left) (2 * seed + 2))

def Samples.arbitrary (n seed : Nat) : Samples := Samples.arbitraryWith n n seed

def Ranges.records : Ranges → Nat
  | .none => 0
  | .node l _ r => 1 + l.records + r.records

def Ranges.height : Ranges → Nat
  | .none => 0
  | .node l _ r => 1 + max l.height r.height

/-- A chain of `n` spans down the left. -/
def Ranges.chain : Nat → Ranges
  | 0 => .none
  | n + 1 => .node (Ranges.chain n) ⟨UInt64.ofNat n, ⟨n % 3 == 0, Float32.ofNat n⟩, Float.ofNat n⟩
      .none

/-- A tree of at most `n` spans and `fuel` levels from the arbitrary words of `seed`. -/
def Ranges.arbitraryWith : Nat → Nat → Nat → Ranges
  | 0, _, _ | _, 0, _ => .none
  | fuel + 1, n + 1, seed =>
    let left := (rw (seed + 1)).toNat % (n + 1)
    .node (Ranges.arbitraryWith fuel left (2 * seed + 1))
      ⟨rw (seed + 2), ⟨(rw (seed + 3)).toNat % 2 == 0, Float32.ofBits (rw (seed + 4)).toUInt32⟩,
        rf (seed + 5)⟩
      (Ranges.arbitraryWith fuel (n - left) (2 * seed + 2))

def Tinted.records : Tinted → Nat
  | .leaf => 0
  | .node l _ _ r => 1 + l.records + r.records

def f64 (x : Float) : String := s!"f64:{x.toBits}"

def f32 (x : Float32) : String := s!"f32:{x.toBits}"

def cases : IO Unit := do
  let trees := [Samples.empty, .mark true 1.5, .mark false (-0.0),
      .sample .empty true 2.0 0.5 3 .empty,
      .sample (.mark true 1.5) false (0.0 / 0.0) (1.0 / 0.0) maxU (.mark false 4.0),
      Samples.chain 997, Samples.chain 998, Samples.chain 999, Samples.chain 1200] ++
    (List.range 20).map fun i => Samples.arbitrary (8 * i) i
  for (f, w) in [(true, 1.5), (false, -0.0), (true, 0.0 / 0.0)] do
    IO.println s!"typedtrees|mark|records-u64|{if f then "i64:1" else "i64:0"} {f64 w}|\
      {records (mark f w)}|1|1"
  for t in trees do
    let n := t.records
    let arg := recordsArg t
    IO.println s!"typedtrees|keep|records-u64|{arg}|{records (keep t)}|{n}|{n}"
    IO.println s!"typedtrees|double|records-u64|{arg}|{records (double t)}|{2 * n + 1}|\
      {2 * n + 1}"
    IO.println s!"typedtrees|rightWeight|f64|{f64 1.0} {arg}|{(rightWeight 1.0 t).toBits}|{n}|{n}"
    if t.height < 1000 then
      IO.println s!"typedtrees|flip|records-u64|{arg}|{records (flip t)}|{n}|{n}"
      for k in [2.0, -0.5] do
        IO.println s!"typedtrees|scale|records-u64|{f64 k} {arg}|{records (scale k t)}|{n}|{n}"
      IO.println s!"typedtrees|weight|f64|{arg}|{(weight t).toBits}|{n}|{n}"
      IO.println s!"typedtrees|flags|i64|{arg}|{flags t}|{n}|{n}"
      IO.println s!"typedtrees|offsets|f32|{arg}|{(offsets t).toBits}|{n}|{n}"
    else
      IO.println s!"typedtrees|flip|records-u64|{arg}|trap"
      IO.println s!"typedtrees|scale|records-u64|{f64 2.0} {arg}|trap"
      IO.println s!"typedtrees|weight|f64|{arg}|trap"
      IO.println s!"typedtrees|flags|i64|{arg}|trap"
      IO.println s!"typedtrees|offsets|f32|{arg}|trap"
  for l in trees.take 5 do
    for r in trees.take 5 do
      let n := l.records + r.records + 1
      let args := s!"{recordsArg l} i64:1 {f64 2.5} {f32 0.75} i64:9 {recordsArg r}"
      IO.println s!"typedtrees|sample|records-u64|{args}|{records (sample l true 2.5 0.75 9 r)}|\
        {n}|{n}"
  let ranges := [Ranges.none, span .none 1 true 0.5 2.0 .none,
      span (span .none maxU false (0.0 / 0.0) (-0.0) .none) 0 true (1.0 / 0.0) 3.5 .none,
      Ranges.chain 998, Ranges.chain 999, Ranges.chain 1200] ++
    (List.range 20).map fun i => Ranges.arbitraryWith (8 * i) (8 * i) (i + 3)
  for t in ranges do
    let n := t.records
    let arg := recordsArg t
    IO.println s!"typedtrees|keepRanges|records-u64|{arg}|{records (keepRanges t)}|{n}|{n}"
    IO.println s!"typedtrees|bump|records-u64|{arg}|{records (bump t)}|{n}|{n}"
    let s := rootSpan t
    IO.println s!"typedtrees|rootSpan|list:i64,i64,f32,f64|{arg}|{s.count} \
      {if s.mark.flag then 1 else 0} {s.mark.level.toBits} {s.weight.toBits}|{n}|{n}"
    IO.println s!"typedtrees|leftWeight|f64|{f64 0.5} {arg}|{(leftWeight 0.5 t).toBits}|{n}|{n}"
    if t.height < 1000 then
      IO.println s!"typedtrees|counts|i64|{arg}|{counts t}|{n}|{n}"
      IO.println s!"typedtrees|settle|records-u64|{arg}|{records (settle t)}|{n}|{n}"
    else
      IO.println s!"typedtrees|counts|i64|{arg}|trap"
      IO.println s!"typedtrees|settle|records-u64|{arg}|trap"
  for l in ranges.take 3 do
    for r in ranges.take 3 do
      let n := l.records + r.records + 1
      let args := s!"{recordsArg l} i64:5 i64:1 {f32 0.25} {f64 (-1.5)} {recordsArg r}"
      IO.println s!"typedtrees|span|records-u64|{args}|{records (span l 5 true 0.25 (-1.5) r)}|\
        {n}|{n}"
  let tints := [Tinted.leaf, tinted .leaf .red 1 .leaf, tinted .leaf .black maxU .leaf,
    tinted (tinted .leaf .black 2 .leaf) .red 3 (tinted .leaf .red 4 .leaf)]
  for t in tints do
    let n := t.records
    let arg := recordsArg t
    IO.println s!"typedtrees|blacken|records-u64|{arg}|{records (blacken t)}|{n}|{n}"
    IO.println s!"typedtrees|redRoot|i64|{arg}|{if redRoot t then 1 else 0}|{n}|{n}"
    let (c, k) := rootTint t
    IO.println s!"typedtrees|rootTint|list:i64,i64|{arg}|{Flat.flat c} {k}|{n}|{n}"
  for l in tints.take 2 do
    for r in tints.take 2 do
      for c in [Tint.red, .black] do
        let n := l.records + r.records + 1
        let args := s!"{recordsArg l} i64:{Flat.flat c} i64:6 {recordsArg r}"
        IO.println s!"typedtrees|tinted|records-u64|{args}|{records (tinted l c 6 r)}|{n}|{n}"

end Verified.Examples.TypedTrees
