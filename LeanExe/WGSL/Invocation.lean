import LeanExe.WGSL.Accumulate
import LeanExe.WGSL.Index
import LeanExe.WGSL.Obligations

namespace LeanExe.WGSL.Invocation

/-- Three separate storage objects. A host binding theorem must establish that
the concrete bindings realize these disjoint objects and declared lengths. -/
structure Buffers where
  a : WordBuffer
  b : WordBuffer
  sizeA : Nat
  sizeB : Nat
  sizeC : Nat

def Buffers.Valid (buffers : Buffers) (config : GemmConfig) : Prop :=
  config.elementsA ≤ buffers.sizeA ∧ config.elementsB ≤ buffers.sizeB ∧
    config.elementsC ≤ buffers.sizeC

inductive Error where
  | loadA | loadB | storeC
  deriving DecidableEq, Repr

structure Write where
  address : Nat
  value : UInt32
  deriving DecidableEq, Repr

inductive State where
  | entry
  | loop (k : Nat) (acc : UInt32)
  | done (write : Option Write)
  | error (reason : Error)
  deriving DecidableEq, Repr

/-- Macro steps for the single supported parsed body. An iteration contains
read-only loads and one profile-selected arithmetic update; its only store is
after the loop. Thus iterations need no shared-memory synchronization. Index
lemmas justify natural indices and counters against the shader's u32 values. -/
inductive Step (s : ScalarSemantics) (p : Profile) (config : GemmConfig)
    (buffers : Buffers) (row col : Nat) : State → State → Prop where
  | enter : row < config.rows → col < config.cols →
      Step s p config buffers row col .entry (.loop 0 0)
  | skip : ¬ (row < config.rows ∧ col < config.cols) →
      Step s p config buffers row col .entry (.done none)
  | iterate {k acc result} : k < config.inner →
      row * config.inner + k < buffers.sizeA →
      k * config.cols + col < buffers.sizeB →
      Accumulate s p acc (buffers.a (row * config.inner + k))
        (buffers.b (k * config.cols + col)) result →
      Step s p config buffers row col (.loop k acc) (.loop (k + 1) result)
  | loadA {k acc} : k < config.inner →
      ¬ row * config.inner + k < buffers.sizeA →
      Step s p config buffers row col (.loop k acc) (.error .loadA)
  | loadB {k acc} : k < config.inner →
      row * config.inner + k < buffers.sizeA →
      ¬ k * config.cols + col < buffers.sizeB →
      Step s p config buffers row col (.loop k acc) (.error .loadB)
  | store {k acc} : config.inner ≤ k →
      row * config.cols + col < buffers.sizeC →
      Step s p config buffers row col (.loop k acc)
        (.done (some ⟨row * config.cols + col, acc⟩))
  | storeC {k acc} : config.inner ≤ k →
      ¬ row * config.cols + col < buffers.sizeC →
      Step s p config buffers row col (.loop k acc) (.error .storeC)

inductive Steps (step : State → State → Prop) : State → State → Prop where
  | refl (state) : Steps step state state
  | next {start middle finish} : step start middle → Steps step middle finish →
      Steps step start finish

def remaining (config : GemmConfig) : State → Nat
  | .entry => config.inner + 2
  | .loop k _ => config.inner - k + 1
  | .done _ | .error _ => 0

theorem Step.decreases {s p config buffers row col x y}
    (h : Step s p config buffers row col x y) : remaining config y < remaining config x := by
  cases h <;> simp only [remaining] <;> omega

/-- This rules out every infinite sequence of actual invocation transitions;
it does not assume that only terminating executions belong to the semantics. -/
theorem no_infinite_steps (s p config buffers row col) :
    ¬ ∃ trace : Nat → State, ∀ n, Step s p config buffers row col (trace n) (trace (n + 1)) := by
  rintro ⟨trace, ht⟩
  have bound : ∀ n, remaining config (trace n) + n ≤ remaining config (trace 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have h := (ht n).decreases; omega
  have h := bound (remaining config (trace 0) + 1)
  omega

/-- Reachable-state invariant links the operational accumulator to the separate
matrix relation, and retains the guard and loop bounds needed for safety. -/
def Invariant (s : ScalarSemantics) (p : Profile) (config : GemmConfig)
    (buffers : Buffers) (row col : Nat) : State → Prop
  | .entry => True
  | .loop k acc => row < config.rows ∧ col < config.cols ∧ k ≤ config.inner ∧
      Dot s p config buffers.a buffers.b row col k acc
  | .done none => ¬ (row < config.rows ∧ col < config.cols)
  | .done (some w) => row < config.rows ∧ col < config.cols ∧
      w.address = row * config.cols + col ∧
      Dot s p config buffers.a buffers.b row col config.inner w.value
  | .error _ => False

theorem Step.preserves {s p buffers row col x y} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (hi : Invariant s p kernel.ast.config buffers row col x)
    (h : Step s p kernel.ast.config buffers row col x y) :
    Invariant s p kernel.ast.config buffers row col y := by
  cases h with
  | enter hr hc => exact ⟨hr, hc, Nat.zero_le _, .zero⟩
  | skip h => exact h
  | iterate hk _ _ update => exact ⟨hi.1, hi.2.1, by omega, .next hi.2.2.2 update⟩
  | loadA hk bad =>
      have h := (Index.cell_bounds kernel hi.1 hi.2.1 hk).a
      exact bad (Nat.lt_of_lt_of_le h hb.1)
  | loadB hk _ bad =>
      have h := (Index.cell_bounds kernel hi.1 hi.2.1 hk).b
      exact bad (Nat.lt_of_lt_of_le h hb.2.1)
  | store hk _ =>
      have equal : _ = kernel.ast.config.inner := Nat.le_antisymm hi.2.2.1 hk
      exact ⟨hi.1, hi.2.1, rfl, equal ▸ hi.2.2.2⟩
  | storeC _ bad =>
      have h := Index.linear_lt hi.1 hi.2.1
      exact bad (Nat.lt_of_lt_of_le h hb.2.2)

theorem Steps.preserves {s p buffers row col x y} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (hi : Invariant s p kernel.ast.config buffers row col x)
    (h : Steps (Step s p kernel.ast.config buffers row col) x y) :
    Invariant s p kernel.ast.config buffers row col y := by
  induction h with
  | refl => exact hi
  | next first _ ih => exact ih (first.preserves kernel hb hi)

theorem safe {s p buffers row col err} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config) :
    ¬ Steps (Step s p kernel.ast.config buffers row col) .entry (.error err) := by
  intro h
  exact Steps.preserves (x := .entry) kernel hb True.intro h

theorem progress {s p c buffers row col state} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c)
    (hi : Invariant s p kernel.ast.config buffers row col state) :
    (∃ write, state = .done write) ∨
      ∃ next, Step s p kernel.ast.config buffers row col state next := by
  cases state with
  | entry =>
      right
      by_cases h : row < kernel.ast.config.rows ∧ col < kernel.ast.config.cols
      · exact ⟨_, .enter h.1 h.2⟩
      · exact ⟨_, .skip h⟩
  | loop k acc =>
      right
      by_cases hk : k < kernel.ast.config.inner
      · have bounds := Index.cell_bounds kernel hi.1 hi.2.1 hk
        obtain ⟨result, hu⟩ := Accumulate.exists_of_total hc he ht acc
          (buffers.a (row * kernel.ast.config.inner + k))
          (buffers.b (k * kernel.ast.config.cols + col))
        exact ⟨_, .iterate hk (Nat.lt_of_lt_of_le bounds.a hb.1)
          (Nat.lt_of_lt_of_le bounds.b hb.2.1) hu⟩
      · exact ⟨_, .store (by omega)
          (Nat.lt_of_lt_of_le (Index.linear_lt hi.1 hi.2.1) hb.2.2)⟩
  | done write => exact .inl ⟨write, rfl⟩
  | error _ => exact False.elim hi

theorem finishes {s p c buffers row col state} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c)
    (hi : Invariant s p kernel.ast.config buffers row col state) :
    ∃ write, Steps (Step s p kernel.ast.config buffers row col) state (.done write) := by
  generalize hm : remaining kernel.ast.config state = n
  induction n using Nat.strongRecOn generalizing state with
  | ind n ih =>
      rcases progress kernel hb hc he ht hi with ⟨write, rfl⟩ | ⟨next, step⟩
      · exact ⟨write, .refl _⟩
      · obtain ⟨write, rest⟩ := ih (remaining kernel.ast.config next)
          (hm ▸ step.decreases) (step.preserves kernel hb hi) rfl
        exact ⟨write, .next step rest⟩

structure Input where
  buffers : Buffers
  row : Nat
  col : Nat

/-- Each behavior is defined by operational steps, including a real infinite
trace case and explicit error reachability. Runtime scheduling is external. -/
def model (s : ScalarSemantics) : ExecutionModel CheckedGemm Input (Option Write) Error where
  behavior p kernel input outcome :=
    let step := Step s p kernel.ast.config input.buffers input.row input.col
    match outcome with
    | .success write => Steps step .entry (.done write)
    | .error err => Steps step .entry (.error err)
    | .diverges => ∃ trace : Nat → State, trace 0 = .entry ∧
        ∀ n, step (trace n) (trace (n + 1))

theorem execution {s p c} (kernel : CheckedGemm) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c) :
    ExecutionTheorem (model s) p kernel
      (fun input => input.buffers.Valid kernel.ast.config)
      (fun input output => Invariant s p kernel.ast.config input.buffers
        input.row input.col (.done output)) where
  terminates input hb := ⟨finishes kernel hb hc he ht True.intro, by
    rintro ⟨trace, _, steps⟩
    exact no_infinite_steps s p kernel.ast.config input.buffers input.row input.col ⟨trace, steps⟩⟩
  safe _ hb _ := safe kernel hb
  corresponds _ _ hb steps := Steps.preserves (x := .entry) kernel hb True.intro steps

#print axioms no_infinite_steps
#print axioms safe
#print axioms finishes
#print axioms execution

end LeanExe.WGSL.Invocation
