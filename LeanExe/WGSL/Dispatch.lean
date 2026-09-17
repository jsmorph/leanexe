import LeanExe.WGSL.Invocation

namespace LeanExe.WGSL.Dispatch

structure Thread where
  row : Nat
  col : Nat
  state : Invocation.State

def Thread.coordinate (thread : Thread) : Nat × Nat := (thread.row, thread.col)

/-- Any live invocation can take the next transition. The order is unrestricted;
read-only A/B inputs are shared and each final C store remains in its thread. -/
inductive Step (s : ScalarSemantics) (p : Profile) (config : GemmConfig)
    (buffers : Invocation.Buffers) : List Thread → List Thread → Prop where
  | head {row col x y tail} : Invocation.Step s p config buffers row col x y →
      Step s p config buffers (⟨row, col, x⟩ :: tail) (⟨row, col, y⟩ :: tail)
  | tail {thread before after} : Step s p config buffers before after →
      Step s p config buffers (thread :: before) (thread :: after)

inductive Steps (step : List Thread → List Thread → Prop) : List Thread → List Thread → Prop where
  | refl (threads) : Steps step threads threads
  | next {start middle finish} : step start middle → Steps step middle finish →
      Steps step start finish

def measure (config : GemmConfig) : List Thread → Nat
  | [] => 0
  | thread :: rest => Invocation.remaining config thread.state + measure config rest

theorem Step.decreases {s p config buffers before after}
    (h : Step s p config buffers before after) : measure config after < measure config before := by
  induction h with
  | head step => simpa only [measure] using Nat.add_lt_add_right step.decreases _
  | tail _ ih => exact Nat.add_lt_add_left ih _

theorem no_infinite_steps (s p config buffers) :
    ¬ ∃ trace : Nat → List Thread, ∀ n, Step s p config buffers (trace n) (trace (n + 1)) := by
  rintro ⟨trace, ht⟩
  have bound : ∀ n, measure config (trace n) + n ≤ measure config (trace 0) := by
    intro n
    induction n with
    | zero => omega
    | succ n ih => have h := (ht n).decreases; omega
  have h := bound (measure config (trace 0) + 1)
  omega

def Invariant (s : ScalarSemantics) (p : Profile) (config : GemmConfig)
    (buffers : Invocation.Buffers) (threads : List Thread) : Prop :=
  ∀ thread ∈ threads, Invocation.Invariant s p config buffers thread.row thread.col thread.state

theorem Step.preserves {s p buffers before after} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (h : Step s p kernel.ast.config buffers before after)
    (hi : Invariant s p kernel.ast.config buffers before) :
    Invariant s p kernel.ast.config buffers after := by
  induction h with
  | head step =>
      intro thread member
      rcases List.mem_cons.mp member with rfl | member
      · have initial := hi _ (List.mem_cons_self ..)
        exact step.preserves kernel hb initial
      · exact hi _ (List.mem_cons_of_mem _ member)
  | tail _ ih =>
      intro thread member
      rcases List.mem_cons.mp member with rfl | member
      · exact hi _ (by simp)
      · exact ih (fun t ht => hi t (List.mem_cons_of_mem _ ht)) thread member

theorem Step.coordinates {s p config buffers before after}
    (h : Step s p config buffers before after) :
    after.map Thread.coordinate = before.map Thread.coordinate := by
  induction h with
  | head => rfl
  | tail _ ih => exact congrArg (_ :: ·) ih

theorem Steps.preserves {s p buffers before after} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (h : Steps (Step s p kernel.ast.config buffers) before after)
    (hi : Invariant s p kernel.ast.config buffers before) :
    Invariant s p kernel.ast.config buffers after ∧
      after.map Thread.coordinate = before.map Thread.coordinate := by
  induction h with
  | refl => exact ⟨hi, rfl⟩
  | next step _ ih =>
      obtain ⟨inv, coords⟩ := ih (step.preserves kernel hb hi)
      exact ⟨inv, coords.trans step.coordinates⟩

def Finished (threads : List Thread) : Prop :=
  ∀ thread ∈ threads, ∃ write, thread.state = .done write

theorem progress {s p c buffers threads} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c)
    (hi : Invariant s p kernel.ast.config buffers threads) :
    Finished threads ∨ ∃ next, Step s p kernel.ast.config buffers threads next := by
  induction threads with
  | nil => exact .inl (by intro t h; cases h)
  | cons thread rest ih =>
      rcases Invocation.progress kernel hb hc he ht (hi thread (by simp)) with
        ⟨write, hw⟩ | ⟨next, step⟩
      · rcases ih (fun t h => hi t (List.mem_cons_of_mem _ h)) with done | ⟨next, step⟩
        · left
          intro t h
          rcases List.mem_cons.mp h with rfl | h
          · exact ⟨write, hw⟩
          · exact done t h
        · exact .inr ⟨_, .tail step⟩
      · exact .inr ⟨_, .head step⟩

theorem finishes {s p c buffers threads} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c)
    (hi : Invariant s p kernel.ast.config buffers threads) :
    ∃ final, Steps (Step s p kernel.ast.config buffers) threads final ∧ Finished final := by
  generalize hm : measure kernel.ast.config threads = n
  induction n using Nat.strongRecOn generalizing threads with
  | ind n ih =>
      rcases progress kernel hb hc he ht hi with done | ⟨next, step⟩
      · exact ⟨threads, .refl _, done⟩
      · obtain ⟨final, steps, done⟩ := ih (measure kernel.ast.config next)
          (hm ▸ step.decreases) (step.preserves kernel hb hi) rfl
        exact ⟨final, .next step steps, done⟩

/-- Write/write conflicts are impossible for different invocation coordinates
in any reachable state. There are no reads of C and no writes to A or B. -/
theorem writes_disjoint {s p config buffers threads t u w v}
    (hi : Invariant s p config buffers threads) (ht : t ∈ threads) (hu : u ∈ threads)
    (htw : t.state = .done (some w)) (huw : u.state = .done (some v))
    (different : t.coordinate ≠ u.coordinate) : w.address ≠ v.address := by
  have ti := hi t ht
  have ui := hi u hu
  rw [htw] at ti
  rw [huw] at ui
  intro equal
  rw [ti.2.2.1, ui.2.2.1] at equal
  obtain ⟨hr, hc⟩ := Index.linear_injective ti.2.1 ui.2.1 equal
  exact different (Prod.ext hr hc)

def store (buffer : WordBuffer) (write : Invocation.Write) : WordBuffer :=
  fun address => if address = write.address then write.value else buffer address

/-- Independent final stores commute at every observable address. This is the
memory fact needed to make completion visibility independent of schedule. -/
theorem store_commutes (buffer : WordBuffer) (a b : Invocation.Write)
    (different : a.address ≠ b.address) : store (store buffer a) b = store (store buffer b) a := by
  funext address
  simp only [store]
  by_cases ha : address = a.address <;> by_cases hb : address = b.address <;> simp_all

#print axioms no_infinite_steps
#print axioms finishes
#print axioms writes_disjoint
#print axioms store_commutes

end LeanExe.WGSL.Dispatch
