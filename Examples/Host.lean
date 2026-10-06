/-! Arguments and results in the kinds of `build/tools/leanexe-wasmtime-host`, for programs on
words and word arrays: a word is one `i64` argument, an array one `array-u64` argument, and a
tuple its components in order.  `lines` writes one sample per line in the format of
`tests/modules/run.sh`. -/

namespace Examples.Host

class HostArgs (α : Type) where
  args : α → List String

instance : HostArgs UInt64 := ⟨fun x => [s!"i64:{x}"]⟩

instance : HostArgs (Array UInt64) :=
  ⟨fun xs => [s!"array-u64:{",".intercalate (xs.toList.map toString)}"]⟩

instance [HostArgs α] [HostArgs β] : HostArgs (α × β) :=
  ⟨fun x => HostArgs.args x.1 ++ HostArgs.args x.2⟩

/-- The host's result kind, and a result as the test runner compares it: a word in decimal, an
array as its words separated by commas. -/
class HostResult (β : Type) where
  kind : String
  render : β → String

instance : HostResult UInt64 := ⟨"i64", toString⟩

instance : HostResult (Array UInt64) :=
  ⟨"array-u64", fun xs => ",".intercalate (xs.toList.map toString)⟩

/-- For each sample, the module, the export, the result kind, the arguments, and `f` of the
sample. -/
def lines [HostArgs α] [HostResult β] (module name : String) (f : α → β) (samples : List α) :
    List String :=
  samples.map fun x =>
    s!"{module}|{name}|{HostResult.kind β}|{" ".intercalate (HostArgs.args x)}|{HostResult.render (f x)}"

/-! Helpers of the module cases: argument and result strings, and inputs that several
examples share. -/

def words (xs : List UInt64) : String := ",".intercalate (xs.map toString)
def arrU (xs : List UInt64) : String := s!"array-u64:{words xs}"
def arrF (xs : List Float) : String := arrU (xs.map Float.toBits)
def chain (xs : List UInt64) : String := s!"chain-u64:{words xs}"
def u (n : UInt64) : String := s!"i64:{n}"
def fl (x : Float) : String := s!"f64:{x.toBits}"

def line (m name kind : String) (args : List String) (expected : String) : IO Unit :=
  IO.println s!"{m}|{name}|{kind}|{" ".intercalate args}|{expected}"

def pair (r : Array UInt64 × Array UInt64) : String := s!"{words r.1.toList},{words r.2.toList}"
def pairKind : String := "list:array-u64,array-u64"
def triple (r : Array UInt64 × Array UInt64 × Array UInt64) : String :=
  s!"{words r.1.toList},{words r.2.1.toList},{words r.2.2.toList}"
def tripleKind : String := "list:array-u64,array-u64,array-u64"

def inf : Float := 1.0 / 0.0
def nan : Float := 0.0 / 0.0
def maxU : UInt64 := 18446744073709551615

/-- Arbitrary words. -/
def rw (i : Nat) : UInt64 := UInt64.ofNat ((i * 0x9E3779B97F4A7C15 + 12345) % 2 ^ 64)
/-- Arbitrary bit patterns as floats. -/
def rf (i : Nat) : Float := Float.ofBits (rw i)
/-- Values from -10 to 10 in steps of 0.01. -/
def small (i : Nat) : Float := (UInt64.ofNat ((i * 2654435761) % 2001)).toFloat / 100.0 - 10.0
/-- Words below `n`. -/
def below (n i : Nat) : UInt64 := UInt64.ofNat ((i * 2654435761 + 7) % n)

def specialFloats : List Float :=
  [0.0, -0.0, 1.0, -1.0, 0.5, inf, -inf, nan, 1e308, -1e308, 5e-324, 2.2250738585072014e-308,
    1e200, 1e-200, 3.0, 7.25]

def wordArrays : List (List UInt64) :=
  [[], [0], [1, 2, 3], [maxU, 2], [maxU, maxU, maxU]] ++
    (List.range 30).map fun i => (List.range (i % 12)).map fun k => rw (17 * i + k)

/-- Triples of special values, arbitrary bit patterns, and moderate values. -/
def floatTriples : List (Float × Float × Float) :=
  let sp := specialFloats.toArray
  let special := (List.range 30).map fun i =>
    (sp[i % sp.size]!, sp[(i / 3 + 5) % sp.size]!, sp[(7 * i + 1) % sp.size]!)
  let random := (List.range 30).map fun i => (rf (3 * i + 500), rf (3 * i + 501), rf (3 * i + 502))
  let moderate := (List.range 20).map fun i => (small (3 * i), small (3 * i + 1), small (3 * i + 2))
  special ++ random ++ moderate

def floatArrays : List (List Float) :=
  [[], [0.0], [-0.0], [1.0, 2.0, 3.0], [inf], [inf, -inf], [nan, 1.0], [1e200, 1e200], [5e-324, 5e-324],
    [1.0, 1e-16, 1e-16], [1e-16, 1e-16, 1.0], [1.7976931348623157e308, 1.0]] ++
    ((List.range 20).map fun i => (List.range (i % 9)).map fun k => rf (13 * i + k + 700)) ++
    ((List.range 20).map fun i => (List.range (i % 9 + 1)).map fun k => small (11 * i + k))

end Examples.Host
