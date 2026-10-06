/-! Arguments and results in the kinds of `build/tools/leanexe-wasmtime-host`, for programs on
words and word arrays: a word is one `i64` argument, an array one `array-u64` argument, and a
tuple its components in order.  `lines` writes one sample per line in the format of
`tests/modules/run.sh`. -/

namespace Project.Demo

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

end Project.Demo
