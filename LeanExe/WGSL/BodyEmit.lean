import LeanExe.WGSL.Source

namespace LeanExe.WGSL.Source

private def indexText (indices : List String) : Index → String
  | .lit n => s!"{n}u"
  | .row => "row"
  | .col => "col"
  | .local n => indices[n]?.getD "INVALID_INDEX"
  | .add a b => s!"({indexText indices a} + {indexText indices b})"
  | .mul a b => s!"({indexText indices a} * {indexText indices b})"

private structure Emission where
  serial : Nat := 0
  lines : Array String := #[]

private abbrev Emit := StateM Emission

private def fresh (stem : String) : Emit String := do
  let state ← get
  set { state with serial := state.serial + 1 }
  pure s!"{stem}{state.serial}"

private def line (indent : Nat) (text : String) : Emit Unit :=
  modify fun state => { state with lines := state.lines.push (String.ofList (List.replicate indent ' ') ++ text) }

private def bindWord (indent : Nat) (expr : String) : Emit String := do
  let name ← fresh "v"
  line indent s!"let {name}: f32 = {expr};"
  pure name

private def emitTerm (indent : Nat) (indices words : List String) : Term → Emit String
  | .lit word => bindWord indent s!"bitcast<f32>({word.toNat}u)"
  | .local n => pure (words[n]?.getD "INVALID_WORD")
  | .readA i => bindWord indent s!"a[{indexText indices i}]"
  | .readB i => bindWord indent s!"b[{indexText indices i}]"
  | .add a b => do
      let x ← emitTerm indent indices words a
      let y ← emitTerm indent indices words b
      bindWord indent s!"{x} + {y}"
  | .mul a b => do
      let x ← emitTerm indent indices words a
      let y ← emitTerm indent indices words b
      bindWord indent s!"{x} * {y}"
  | .letE value body => do
      let name ← emitTerm indent indices words value
      emitTerm indent indices (name :: words) body
  | .fold count initial body => do
      let initialName ← emitTerm indent indices words initial
      let acc ← fresh "acc"
      let k ← fresh "k"
      line indent s!"var {acc}: f32 = {initialName};"
      line indent s!"for (var {k}: u32 = 0u; {k} < {count}u; {k} = {k} + 1u) \{"
      let value ← emitTerm (indent + 2) (k :: indices) (acc :: words) body
      line (indent + 2) s!"{acc} = {value};"
      line indent "}"
      pure acc

/-- Only dispatch/buffer declarations are fixed. Every computation statement
comes from the supplied expression tree, including fold bodies and indices. -/
def emit (shape : Shape) (term : Term) : String := Id.run do
  let (result, state) := (emitTerm 2 [] [] term).run {}
  pure <| String.intercalate "\n" <| [
    "// Lean body compiler: binary32 word interface",
    s!"const M: u32 = {shape.rows}u;",
    s!"const N: u32 = {shape.cols}u;",
    "@group(0) @binding(0) var<storage, read> a: array<f32>;",
    "@group(0) @binding(1) var<storage, read> b: array<f32>;",
    "@group(0) @binding(2) var<storage, read_write> c: array<f32>;",
    "@compute @workgroup_size(8, 8, 1)",
    "fn lean_kernel(@builtin(global_invocation_id) gid: vec3<u32>) {",
    "  let col: u32 = gid.x;",
    "  let row: u32 = gid.y;",
    "  if (col >= N || row >= M) { return; }"
  ] ++ state.lines.toList ++ [s!"  c[row * N + col] = {result};", "}", ""]

end LeanExe.WGSL.Source
