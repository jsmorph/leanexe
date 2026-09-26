import LeanExe.WGSL.UIntParse

namespace LeanExe.WGSL.UInt

/-- A line-oriented certificate path for large straight-line shaders. Every
line is lexed independently; multiline comments are excluded from this subset.
The accepted lines are joined with newlines to identify the exact shader text. -/
def lineStep (locals : Locals) (line : String) : Option Locals := do
  let tokens ← (tokenize line).toOption
  match tokens with
  | "let" :: name :: ":" :: "u32" :: "=" :: rest =>
    if (lookup locals name).isSome || !(name.startsWith "v") then none else do
      let rhs ← rest.reverse.tail?
      if rest.getLast? != some ";" then none else do
        let value ← rhs? locals rhs.reverse
        some ((name,value)::locals)
  | _ => none

def steps (lines : List String) (locals : Locals) : Option Locals :=
  lines.foldlM lineStep locals

theorem steps_append {a b : List String} {start middle finish : Locals}
    (ha : steps a start = some middle) (hb : steps b middle = some finish) :
    steps (a++b) start = some finish := by
  unfold steps at *
  rw [List.foldlM_append]
  simp [ha, hb]

def headerLines : List String := [
  "@group(0) @binding(0) var<storage, read> scene: array<u32>;",
  "@group(0) @binding(1) var<storage, read> directions: array<u32>;",
  "@group(0) @binding(2) var<storage, read> params: array<u32>;",
  "@group(0) @binding(3) var<storage, read_write> results: array<u32>;",
  "@compute @workgroup_size(4)",
  "fn lidar(@builtin(global_invocation_id) gid: vec3<u32>) {",
  "  if (gid.x >= 4u) { return; }"]

def footer (output : String) : List String := ["  results[gid.x] = " ++ output ++ ";", "}", ""]

/-- A compositional certificate checks every statement and the final value,
while the fixed surrounding grammar establishes bindings and lane ownership. -/
def Certified (source : String) (code : Expr) : Prop :=
  ∃ lines locals output,
    steps lines [] = some locals ∧ lookup locals output = some code ∧
    source = String.intercalate "\n" (headerLines ++ lines ++ footer output)

/-- The parsed subset has immutable reads, bounded straight-line evaluation,
one guarded lane-owned write, and no atomics or inter-lane communication.
External WebGPU execution is required to implement this subset semantics. -/
def Executes (source : String) (input : Input) (output : Nat) : Prop :=
  ∃ code, (parse source = some code ∨ Certified source code) ∧ code.eval32 input = output

theorem parsed_executes {source : String} {code : Expr}
    (parsed : parse source = some code) (input : Input) :
    Executes source input (code.eval32 input) := ⟨code, Or.inl parsed, rfl⟩

theorem certified_executes {source : String} {code : Expr}
    (certified : Certified source code) (input : Input) :
    Executes source input (code.eval32 input) := ⟨code, Or.inr certified, rfl⟩

end LeanExe.WGSL.UInt
