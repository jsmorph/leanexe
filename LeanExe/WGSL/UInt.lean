import LeanExe.WGSL.Lexer

/-! Small integer expression compiler, alongside the WGSL branch's floating
point body compiler. A lane reads immutable buffers and owns one output word.
Unsigned subtraction is explicitly saturating, implemented with max/subtract.
All shader arithmetic is u32; overflow is modeled, never assumed away. -/
namespace LeanExe.WGSL.UInt

def modulus : Nat := 4294967296

inductive Buffer where
  | scene | params
  deriving Repr, BEq, DecidableEq

inductive Expr where
  | lit (n : Nat)
  | read (buffer : Buffer) (index : Nat)
  | direction
  | add (a b : Expr)
  | mul (a b : Expr)
  | sub (a b : Expr)
  | min (a b : Expr)
  | le (a b : Expr)
  | eq (a b : Expr)
  | both (a b : Expr)
  | choose (condition yes no : Expr)
  deriving Repr, BEq, DecidableEq

structure Input where
  scene : Nat → Nat
  params : Nat → Nat
  direction : Nat

def Expr.eval (input : Input) : Expr → Nat
  | .lit n => n
  | .read .scene i => input.scene i
  | .read .params i => input.params i
  | .direction => input.direction
  | .add a b => a.eval input + b.eval input
  | .mul a b => a.eval input * b.eval input
  | .sub a b => a.eval input - b.eval input
  | .min a b => Nat.min (a.eval input) (b.eval input)
  | .le a b => if a.eval input ≤ b.eval input then 1 else 0
  | .eq a b => if a.eval input = b.eval input then 1 else 0
  | .both a b => if a.eval input ≠ 0 ∧ b.eval input ≠ 0 then 1 else 0
  | .choose c a b => if c.eval input ≠ 0 then a.eval input else b.eval input

/-- The scalar meaning of emitted WGSL u32 expressions, including wrapping. -/
def Expr.eval32 (input : Input) : Expr → Nat
  | .lit n => n % modulus
  | .read .scene i => input.scene i % modulus
  | .read .params i => input.params i % modulus
  | .direction => input.direction % modulus
  | .add a b => (a.eval32 input + b.eval32 input) % modulus
  | .mul a b => (a.eval32 input * b.eval32 input) % modulus
  | .sub a b => a.eval32 input - b.eval32 input
  | .min a b => Nat.min (a.eval32 input) (b.eval32 input)
  | .le a b => if a.eval32 input ≤ b.eval32 input then 1 else 0
  | .eq a b => if a.eval32 input = b.eval32 input then 1 else 0
  | .both a b => if a.eval32 input ≠ 0 ∧ b.eval32 input ≠ 0 then 1 else 0
  | .choose c a b => if c.eval32 input ≠ 0 then a.eval32 input else b.eval32 input

/-- Conservative bound when all data words are at most `cap`. -/
def Expr.bound (cap : Nat) : Expr → Nat
  | .lit n => n
  | .read _ _ | .direction => cap
  | .add a b => a.bound cap + b.bound cap
  | .mul a b => a.bound cap * b.bound cap
  | .sub a _ => a.bound cap
  | .min a b => Nat.min (a.bound cap) (b.bound cap)
  | .le _ _ | .eq _ _ | .both _ _ => 1
  | .choose _ a b => max (a.bound cap) (b.bound cap)

def Expr.Checked (cap : Nat) : Expr → Prop
  | .lit n => n < modulus
  | .read _ _ | .direction => cap < modulus
  | .add a b => a.Checked cap ∧ b.Checked cap ∧ a.bound cap + b.bound cap < modulus
  | .mul a b => a.Checked cap ∧ b.Checked cap ∧ a.bound cap * b.bound cap < modulus
  | .sub a b | .min a b | .le a b | .eq a b | .both a b => a.Checked cap ∧ b.Checked cap
  | .choose c a b => c.Checked cap ∧ a.Checked cap ∧ b.Checked cap

instance checkedDecidable (cap : Nat) : (e : Expr) → Decidable (Expr.Checked cap e)
  | .lit n => inferInstanceAs (Decidable (n < modulus))
  | .read _ _ | .direction => inferInstanceAs (Decidable (cap < modulus))
  | .add a b | .mul a b => @instDecidableAnd _ _ (checkedDecidable cap a)
      (@instDecidableAnd _ _ (checkedDecidable cap b) inferInstance)
  | .sub a b | .min a b | .le a b | .eq a b | .both a b =>
      @instDecidableAnd _ _ (checkedDecidable cap a) (checkedDecidable cap b)
  | .choose c a b => @instDecidableAnd _ _ (checkedDecidable cap c)
      (@instDecidableAnd _ _ (checkedDecidable cap a) (checkedDecidable cap b))

def Input.Bounded (input : Input) (cap : Nat) : Prop :=
  (∀ i, input.scene i ≤ cap) ∧ (∀ i, input.params i ≤ cap) ∧ input.direction ≤ cap

theorem eval_le_bound (e : Expr) (input : Input) (cap : Nat) (h : input.Bounded cap) :
    e.eval input ≤ e.bound cap := by
  induction e with
  | lit => simp [Expr.eval, Expr.bound]
  | read b i => cases b <;> simp only [Expr.eval, Expr.bound]; exact h.1 i; exact h.2.1 i
  | direction => exact h.2.2
  | add a b ha hb => simp only [Expr.eval, Expr.bound]; omega
  | mul a b ha hb => exact Nat.mul_le_mul ha hb
  | sub a b ha hb => simp only [Expr.eval, Expr.bound]; omega
  | min a b ha hb =>
    exact Nat.le_min_of_le_of_le (Nat.le_trans (Nat.min_le_left _ _) ha) (Nat.le_trans (Nat.min_le_right _ _) hb)
  | le | eq | both => simp only [Expr.eval, Expr.bound]; split <;> omega
  | choose c a b hc ha hb => simp only [Expr.eval, Expr.bound]; split <;> omega

theorem exact32 (e : Expr) (input : Input) (cap : Nat)
    (bounded : input.Bounded cap) (checked : e.Checked cap) :
    e.eval32 input = e.eval input := by
  induction e with
  | lit n => exact Nat.mod_eq_of_lt checked
  | read b i =>
    cases b <;> apply Nat.mod_eq_of_lt
    · exact Nat.lt_of_le_of_lt (bounded.1 i) checked
    · exact Nat.lt_of_le_of_lt (bounded.2.1 i) checked
  | direction => exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt bounded.2.2 checked)
  | add a b ha hb =>
    simp only [Expr.eval32, Expr.eval, ha checked.1, hb checked.2.1]
    apply Nat.mod_eq_of_lt
    have := eval_le_bound a input cap bounded
    have := eval_le_bound b input cap bounded
    have := checked.2.2
    omega
  | mul a b ha hb =>
    simp only [Expr.eval32, Expr.eval, ha checked.1, hb checked.2.1]
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
      (Nat.mul_le_mul (eval_le_bound a input cap bounded) (eval_le_bound b input cap bounded)) checked.2.2)
  | sub a b ha hb | min a b ha hb | le a b ha hb | eq a b ha hb | both a b ha hb =>
    simp only [Expr.eval32, Expr.eval, ha checked.1, hb checked.2]
  | choose c a b hc ha hb =>
    simp only [Expr.eval32, Expr.eval, hc checked.1, ha checked.2.1, hb checked.2.2]

structure Code where
  lines : Array String := #[]
  cache : List (Expr × String) := []

private def fresh (e : Expr) (rhs : String) : StateM Code String := do
  let state ← get
  let name := s!"v{state.lines.size}"
  set ({lines := state.lines.push s!"  let {name}: u32 = {rhs};", cache := (e,name)::state.cache} : Code)
  return name

/-- Local CSE keeps the emitted geometry readable and linear in expression DAG size. -/
def Expr.emit (e : Expr) : StateM Code String := do
  if let some (_,name) := (← get).cache.find? (fun p => p.1 == e) then return name
  let rhs ← match e with
    | .lit n => pure s!"{n}u"
    | .read b i => pure s!"{if b == .scene then "scene" else "params"}[{i}u]"
    | .direction => pure "directions[gid.x]"
    | .add a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"{x} + {y}"
    | .mul a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"{x} * {y}"
    | .sub a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"max({x}, {y}) - {y}"
    | .min a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"min({x}, {y})"
    | .le a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"select(0u, 1u, {x} <= {y})"
    | .eq a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"select(0u, 1u, {x} == {y})"
    | .both a b =>
      let x ← a.emit; let y ← b.emit
      pure s!"select(0u, 1u, ({x} != 0u) && ({y} != 0u))"
    | .choose c a b =>
      let condition ← c.emit; let yes ← a.emit; let no ← b.emit
      pure s!"select({no}, {yes}, {condition} != 0u)"
  fresh e rhs

def shader (e : Expr) (count : Nat) : String :=
  let (out,code) := e.emit.run {}
  String.intercalate "\n" ([
    "@group(0) @binding(0) var<storage, read> scene: array<u32>;",
    "@group(0) @binding(1) var<storage, read> directions: array<u32>;",
    "@group(0) @binding(2) var<storage, read> params: array<u32>;",
    "@group(0) @binding(3) var<storage, read_write> results: array<u32>;",
    "@compute @workgroup_size(4)",
    "fn lidar(@builtin(global_invocation_id) gid: vec3<u32>) {",
    "  if (gid.x >= " ++ toString count ++ "u) { return; }"] ++ code.lines.toList ++
    [s!"  results[gid.x] = {out};", "}", ""])

end LeanExe.WGSL.UInt
