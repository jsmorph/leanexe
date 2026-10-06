import Examples.Gpt32.Program

/-!
The programs that run GPT-2's binary32 step on `leanexe-webgpu-host session`.  A program is a
list of typed items over named buffers: a kernel call, a word, a float, an empty array, or a
file.  Each item becomes one or two host commands, and `Cmd.line` prints a command as the host
reads it.  `Examples/Gpt32/Exec.lean` gives both levels their meaning.

Word constants have names by role and are written at the start of each step.  The caches of a
layer alternate between two names by the parity of the position, so the `append` of position `p`
replaces the buffer that held the caches through position `p - 2`.
-/

namespace Examples.Gpt32

open Examples.Gpt32

inductive Field where
  | g1 | b1 | wq | bq | wk | bk | wv | bv | wo | bo | g2 | b2 | wfc | bfc | wproj | bproj
  deriving DecidableEq, Repr

def Field.all : List Field :=
  [.g1, .b1, .wq, .bq, .wk, .bk, .wv, .bv, .wo, .bo, .g2, .b2, .wfc, .bfc, .wproj, .bproj]

def Field.get (w : Layer32) : Field → Array Float32
  | .g1 => w.g1 | .b1 => w.b1 | .wq => w.wq | .bq => w.bq | .wk => w.wk | .bk => w.bk
  | .wv => w.wv | .bv => w.bv | .wo => w.wo | .bo => w.bo | .g2 => w.g2 | .b2 => w.b2
  | .wfc => w.wfc | .bfc => w.bfc | .wproj => w.wproj | .bproj => w.bproj

def Field.name : Field → String
  | .g1 => "g1" | .b1 => "b1" | .wq => "wq" | .bq => "bq" | .wk => "wk" | .bk => "bk"
  | .wv => "wv" | .bv => "bv" | .wo => "wo" | .bo => "bo" | .g2 => "g2" | .b2 => "b2"
  | .wfc => "wfc" | .bfc => "bfc" | .wproj => "wproj" | .bproj => "bproj"

/-- A buffer of the session: an activation of the step, the scores of chunk `c`, a weight, the
caches of layer `l` with parity `b`, or a word or float constant. -/
inductive Buf where
  | x | h1 | q | k | v | sc | mx | sm | pw | o | a | r | h2 | m1 | g | m2 | hf
  | z (c : Nat)
  | wte (c : Nat)
  | wpe | gf | bf
  | layer (l : Nat) (field : Field)
  | kc (l b : Nat)
  | vc (l b : Nat)
  | pos | base | top | row | width | hidden | heads | scoreLen | rowCount | nf
  deriving DecidableEq, Repr

def Buf.name : Buf → String
  | .x => "x" | .h1 => "h1" | .q => "q" | .k => "k" | .v => "v" | .sc => "sc" | .mx => "mx"
  | .sm => "sm" | .pw => "pw" | .o => "o" | .a => "a" | .r => "r" | .h2 => "h2" | .m1 => "m1"
  | .g => "g" | .m2 => "m2" | .hf => "hf"
  | .z c => s!"z{c}"
  | .wte c => s!"wte{c}"
  | .wpe => "wpe" | .gf => "gf" | .bf => "bf"
  | .layer l f => s!"l{l}_{f.name}"
  | .kc l b => s!"kc{l}_{b}"
  | .vc l b => s!"vc{l}_{b}"
  | .pos => "pos" | .base => "base" | .top => "top" | .row => "row" | .width => "width"
  | .hidden => "hidden" | .heads => "heads" | .scoreLen => "scorelen" | .rowCount => "rowcount"
  | .nf => "nf"

inductive KernelName where
  | embed | layerNorm | linear | append | scores | headMax | headSum | probs | mix | add | gelu
  | logits
  deriving DecidableEq, Repr

def KernelName.all : List KernelName :=
  [.embed, .layerNorm, .linear, .append, .scores, .headMax, .headSum, .probs, .mix, .add, .gelu,
   .logits]

def KernelName.name : KernelName → String
  | .embed => "embed" | .layerNorm => "layerNorm" | .linear => "linear" | .append => "append"
  | .scores => "scores" | .headMax => "headMax" | .headSum => "headSum" | .probs => "probs"
  | .mix => "mix" | .add => "add" | .gelu => "gelu" | .logits => "logits"

/-- The host's name of a kernel's pipeline, which no buffer name equals, since it begins with
`@`. -/
def KernelName.shader (k : KernelName) : String := "@" ++ k.name

/-- A host command: a buffer from a file, a buffer of 32-bit words, an output of `n` elements
(`2 + 2n` words, the first two holding `n`), or a dispatch of `workgroups` workgroups. -/
inductive Cmd where
  | load (b : Buf) (path : String)
  | words (b : Buf) (ws : List UInt32)
  | output (b : Buf) (n : Nat)
  | run (k : KernelName) (workgroups : Nat) (out : Buf) (ins : List Buf)

def Cmd.line : Cmd → String
  | .load b path => s!"load {b.name} {path}"
  | .words b ws => s!"words {b.name} u32:{",".intercalate (ws.map toString)}"
  | .output b n => s!"output {b.name} {n}"
  | .run k w out ins => s!"run {k.shader} {w} {out.name} {" ".intercalate (ins.map Buf.name)}"

/-- An item of a program: a call of kernel `k` filling `out` with `n` elements, a word, a float,
an empty array, or a file holding an array. -/
inductive Item where
  | call (k : KernelName) (n : Nat) (out : Buf) (ins : List Buf)
  | word (b : Buf) (v : UInt64)
  | float (b : Buf) (x : Float32)
  | empty (b : Buf)
  | load (b : Buf) (path : String)

def Item.cmds : Item → List Cmd
  | .call k n out ins => [.output out n, .run k ((n + 63) / 64) out ins]
  | .word b v => [.words b [v.toUInt32, (v >>> 32).toUInt32]]
  | .float b x => [.words b [x.toBits, 0]]
  | .empty b => [.words b [0, 0]]
  | .load b path => [.load b path]

/-- The words of position `p` and the shape. -/
def wordItems (s : Shape32) (token p : UInt64) : List Item :=
  let d := 64 * s.nh
  [.word .pos p, .word .base (p * d), .word .top ((p + 1) * d), .word .row (token % s.chunk),
   .word .width d, .word .hidden s.f, .word .heads s.nh, .word .scoreLen (s.nh * 1024),
   .float .nf d.toFloat32]

/-- The scores of chunk `c`, which has `n` rows. -/
def logitsItems (c : Nat) (n : UInt64) : List Item :=
  [.word .rowCount n, .call .logits n.toNat (.z c) [.hf, .wte c, .rowCount, .width]]

/-- Layer `l` at position `p`. -/
def layerItems (s : Shape32) (p : UInt64) (l : Nat) : List Item :=
  let d := (64 * s.nh).toNat
  let n := (s.nh * 1024).toNat
  let L := Buf.layer l
  let b := (p % 2).toNat
  let b' := ((p + 1) % 2).toNat
  [.call .layerNorm d .h1 [.x, L .g1, L .b1, .width, .nf],
   .call .linear d .q [.h1, L .wq, L .bq, .width, .width],
   .call .linear d .k [.h1, L .wk, L .bk, .width, .width],
   .call .linear d .v [.h1, L .wv, L .bv, .width, .width],
   .call .append ((p + 1).toNat * d) (.kc l b') [.kc l b, .k, .base, .top],
   .call .append ((p + 1).toNat * d) (.vc l b') [.vc l b, .v, .base, .top],
   .call .scores n .sc [.q, .kc l b', .pos, .width, .scoreLen],
   .call .headMax s.nh.toNat .mx [.sc, .pos, .heads],
   .call .headSum s.nh.toNat .sm [.sc, .mx, .pos, .heads],
   .call .probs n .pw [.sc, .mx, .sm, .pos, .scoreLen],
   .call .mix d .o [.pw, .vc l b', .pos, .width],
   .call .linear d .a [.o, L .wo, L .bo, .width, .width],
   .call .add d .r [.x, .a],
   .call .layerNorm d .h2 [.r, L .g2, L .b2, .width, .nf],
   .call .linear s.f.toNat .m1 [.h2, L .wfc, L .bfc, .width, .hidden],
   .call .gelu s.f.toNat .g [.m1],
   .call .linear d .m2 [.g, L .wproj, L .bproj, .hidden, .width],
   .call .add d .x [.r, .m2]]

/-- The step of `token` at position `p`: the scores of chunk `c` end in `z c`. -/
def stepItems (s : Shape32) (token p : UInt64) : List Item :=
  let d := (64 * s.nh).toNat
  wordItems s token p ++
  [.call .embed d .x [.wte (token / s.chunk).toNat, .wpe, .row, .pos, .width]] ++
  (List.range s.layers).flatMap (layerItems s p) ++
  [.call .layerNorm d .hf [.x, .gf, .bf, .width, .nf]] ++
  (List.range s.rows.length).flatMap fun c => logitsItems c s.rows[c]!

/-- The steps of the tokens `ts` at positions `p`, `p + 1`, and so on. -/
def stepsItems (s : Shape32) : List UInt64 → Nat → List Item
  | [], _ => []
  | t :: ts, p => stepItems s t (UInt64.ofNat p) ++ stepsItems s ts (p + 1)

/-- The file of the weight `name` in `dir`, as `tests/gpt32/generate.py` writes it. -/
def weightPath (dir name : String) : String := s!"{dir}/{name}.bin"

/-- The weights and the empty caches of layer `l`. -/
def layerSetup (dir : String) (l : Nat) : List Item :=
  (Field.all.map fun f => .load (.layer l f) (weightPath dir s!"l{l}_{f.name}")) ++
  [.empty (.kc l 0), .empty (.vc l 0)]

/-- The weights from the files of `dir`, and the empty caches of position 0. -/
def setupItems (s : Shape32) (dir : String) : List Item :=
  ((List.range s.rows.length).map fun c => .load (.wte c) (weightPath dir s!"wte{c}")) ++
  [.load .wpe (weightPath dir "wpe"), .load .gf (weightPath dir "gf"),
   .load .bf (weightPath dir "bf")] ++
  (List.range s.layers).flatMap (layerSetup dir)

def Item.lines (items : List Item) : List String :=
  items.flatMap fun i => i.cmds.map Cmd.line

end Examples.Gpt32
