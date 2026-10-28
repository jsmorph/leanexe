import Verified.Reflect.Command

/-! Recursive types whose records hold `Bool`, binary64, binary32, and word fields, structures,
enumerations, and sums beside their children.  Each word, `Bool`, or float occupies one slot: a
`Bool` as 1 or 0, a float as its bit pattern, and a binary32 pattern in the low 32 bits.  A field of
a type with a `Flat` instance occupies one slot for each leaf of its flattening. -/

namespace Verified.Examples.TypedTrees

open LeanExe.Pipeline

/-- Measurements in a tree: nothing, a sample with a flag, a weight, an offset, and a count between
two subtrees, or a mark with a flag and a weight. -/
inductive Samples where
  | empty
  | sample (left : Samples) (flag : Bool) (weight : Float) (offset : Float32) (count : UInt64)
      (right : Samples)
  | mark (flag : Bool) (weight : Float)

/-- `Samples` as records: `empty` is the null pointer, and each other constructor a record of its
index followed by its fields. -/
def Samples.encode : Samples → Node
  | .empty => .null
  | .sample l f w o c r => .record [.word 1, .child l.encode, .word (cond f 1 0), .word w.toBits,
      .word o.toBits.toUInt64, .word c, .child r.encode]
  | .mark f w => .record [.word 2, .word (cond f 1 0), .word w.toBits]

instance : Encode Samples := ⟨Samples.encode⟩

verified_recursive_type Samples

def keep (t : Samples) : Samples := t

def mark (f : Bool) (w : Float) : Samples := .mark f w

def sample (l : Samples) (f : Bool) (w : Float) (o : Float32) (c : UInt64) (r : Samples) :
    Samples :=
  .sample l f w o c r

/-- A sample over two copies of the tree. -/
def double (t : Samples) : Samples := .sample t true 0.5 1.5 2 t

def weight : Samples → Float
  | .empty => 0
  | .sample l _ w _ _ r => weight l + w + weight r
  | .mark _ w => w

def flags : Samples → UInt64
  | .empty => 0
  | .sample l f _ _ _ r => flags l + (if f then 1 else 0) + flags r
  | .mark f _ => if f then 1 else 0

def offsets : Samples → Float32
  | .empty => 0
  | .sample l _ _ o _ r => offsets l + o + offsets r
  | .mark _ _ => 0

/-- The tree with every flag negated, which reuses each record. -/
def flip : Samples → Samples
  | .empty => .empty
  | .sample l f w o c r => .sample (flip l) (!f) w o c (flip r)
  | .mark f w => .mark (!f) w

/-- The tree with each weight multiplied by `k`, each offset doubled, and each count incremented. -/
def scale (k : Float) : Samples → Samples
  | .empty => .empty
  | .sample l f w o c r => .sample (scale k l) f (w * k) (o * 2) (c + 1) (scale k r)
  | .mark f w => .mark f (w * k)

/-- The sum of the weights along the right spine, a loop. -/
def rightWeight (acc : Float) (t : Samples) : Float :=
  match t with
  | .empty => acc
  | .sample _ _ w _ _ r => rightWeight (acc + w) r
  | .mark _ w => acc + w

/-- The mark of a span: a flag and a binary32 level. -/
structure Mark where
  flag : Bool
  level : Float32

instance : Flat Mark (Bool × Float32) := ⟨fun m => (m.flag, m.level)⟩

/-- A span: a count, a mark, and a weight. -/
structure Span where
  count : UInt64
  mark : Mark
  weight : Float

instance : Flat Span (UInt64 × Mark × Float) := ⟨fun s => (s.count, s.mark, s.weight)⟩

/-- A tree of spans.  A span occupies four slots, one for each leaf of its flattening. -/
inductive Ranges where
  | none
  | node (left : Ranges) (span : Span) (right : Ranges)

def Ranges.encode : Ranges → Node
  | .none => .null
  | .node l s r => .record [.child l.encode, .word s.count, .word (cond s.mark.flag 1 0),
      .word s.mark.level.toBits.toUInt64, .word s.weight.toBits, .child r.encode]

instance : Encode Ranges := ⟨Ranges.encode⟩

verified_recursive_type Ranges

def keepRanges (t : Ranges) : Ranges := t

def span (l : Ranges) (c : UInt64) (f : Bool) (v : Float32) (w : Float) (r : Ranges) : Ranges :=
  .node l ⟨c, ⟨f, v⟩, w⟩ r

def counts : Ranges → UInt64
  | .none => 0
  | .node l s r => counts l + s.count + counts r

/-- The tree with each flagged span's level doubled and its flag cleared. -/
def settle : Ranges → Ranges
  | .none => .none
  | .node l s r =>
    .node (settle l) { s with mark := ⟨false, if s.mark.flag then s.mark.level * 2 else
      s.mark.level⟩ } (settle r)

/-- The tree with the root's count incremented. -/
def bump : Ranges → Ranges
  | .none => .none
  | .node l s r => .node l { s with count := s.count + 1 } r

/-- The root's span, or a span of zeros. -/
def rootSpan : Ranges → Span
  | .none => ⟨0, ⟨false, 0⟩, 0⟩
  | .node _ s _ => s

/-- The weights of the spans along the left spine, a loop. -/
def leftWeight (acc : Float) (t : Ranges) : Float :=
  match t with
  | .none => acc
  | .node l s _ => leftWeight (acc + s.weight) l

/-- The tint of a node. -/
inductive Tint where
  | red | black
  deriving DecidableEq

instance : Flat Tint UInt64 := ⟨fun | .red => 0 | .black => 1⟩

/-- A tree whose nodes carry a tint, which occupies one slot.  The words that encode no tint have
no value of the type, so no recursive definition or loop takes the tree as a parameter. -/
inductive Tinted where
  | leaf
  | node (left : Tinted) (tint : Tint) (key : UInt64) (right : Tinted)

def Tinted.encode : Tinted → Node
  | .leaf => .null
  | .node l t k r => .record [.child l.encode, .word (Flat.flat t), .word k, .child r.encode]

instance : Encode Tinted := ⟨Tinted.encode⟩

verified_recursive_type Tinted

def tinted (l : Tinted) (t : Tint) (k : UInt64) (r : Tinted) : Tinted := .node l t k r

/-- The tree with its root tinted black. -/
def blacken (t : Tinted) : Tinted :=
  match t with
  | .leaf => .leaf
  | .node l _ k r => .node l .black k r

/-- Whether the root is red. -/
def redRoot (t : Tinted) : Bool :=
  match t with
  | .leaf => false
  | .node _ c _ _ => c = .red

/-- The root's tint and key, or black and 0. -/
def rootTint (t : Tinted) : Tint × UInt64 :=
  match t with
  | .leaf => (.black, 0)
  | .node _ c k _ => (c, k)

/-- A reading: a binary64 value, a count, or nothing. -/
inductive Reading where
  | value (x : Float)
  | count (n : UInt64)
  | none

instance : Flat Reading (UInt64 × Float × UInt64) := ⟨fun
  | .value x => (0, x, 0)
  | .count n => (1, 0, n)
  | .none => (2, 0, 0)⟩

/-- A tree whose nodes carry a reading, which occupies three slots: its tag, its value, and its
count.  The words that encode no reading have no value of the type, so no recursive definition or
loop takes the tree as a parameter. -/
inductive Logged where
  | nil
  | node (left : Logged) (reading : Reading) (right : Logged)

def Logged.encode : Logged → Node
  | .nil => .null
  | .node l s r => .record [.child l.encode, .word (Flat.flat s).1, .word (Flat.flat s).2.1.toBits,
      .word (Flat.flat s).2.2, .child r.encode]

instance : Encode Logged := ⟨Logged.encode⟩

verified_recursive_type Logged

def logged (l : Logged) (s : Reading) (r : Logged) : Logged := .node l s r

/-- A node that counts `n` between two empty trees. -/
def counted (n : UInt64) : Logged := .node .nil (.count n) .nil

/-- The root's reading as a float: its value, its count, or -1. -/
def rootValue (t : Logged) : Float :=
  match t with
  | .nil => 0
  | .node _ s _ =>
    match s with
    | .value x => x
    | .count n => n.toFloat
    | .none => -1

/-- The tree with the root's count incremented and a missing reading replaced by a count of 0. -/
def tally (t : Logged) : Logged :=
  match t with
  | .nil => .nil
  | .node l s r =>
    match s with
    | .value x => .node l (.value x) r
    | .count n => .node l (.count (n + 1)) r
    | .none => .node l (.count 0) r

verified_compile compiled := [keep, mark, sample, double, weight, flags, offsets, flip, scale,
  rightWeight, keepRanges, span, counts, settle, bump, rootSpan, leftWeight, tinted, blacken,
  redRoot, rootTint, logged, counted, rootValue, tally]

#print axioms compiled.bytes
#print axioms compiled.flip.implements
#print axioms compiled.scale.trapFree
#print axioms compiled.rightWeight.implements
#print axioms compiled.settle.implements
#print axioms compiled.leftWeight.implements
#print axioms compiled.rootTint.implements
#print axioms compiled.rootValue.implements
#print axioms compiled.tally.implements

#guard weight (.sample (.mark true 1.5) false 2.0 0.5 3 .empty) == 3.5
#guard flags (flip (.sample (.mark true 1.5) false 2.0 0.5 3 .empty)) == 1
#guard offsets (scale 2.0 (.sample (.mark true 1.5) false 2.0 0.5 3 .empty)) == 1.0
#guard weight (scale 2.0 (.sample (.mark true 1.5) false 2.0 0.5 3 .empty)) == 7.0
#guard rightWeight 1.0 (.sample .empty true 2.0 0 0 (.mark false 4.0)) == 7.0
#guard flags (double (.mark true 0)) == 3
#guard counts (bump (span .none 2 true 0.5 1.0 (span .none 3 false 1.5 2.0 .none))) == 6
#guard (rootSpan (settle (span .none 2 true 0.5 1.0 .none))).mark.level == 1.0
#guard leftWeight 0 (span (span .none 1 true 0 2.0 .none) 1 true 0 1.0 .none) == 3.0
#guard redRoot (blacken (tinted .leaf .red 1 .leaf)) == false
#guard (rootTint (tinted .leaf .red 7 .leaf)).2 == 7
#guard rootValue (tally (counted 4)) == 5.0
#guard rootValue (tally (logged .nil .none .nil)) == 0.0
#guard rootValue (logged .nil (.value 2.5) (counted 1)) == 2.5

end Verified.Examples.TypedTrees
