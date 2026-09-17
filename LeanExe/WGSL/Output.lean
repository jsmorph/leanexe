import LeanExe.WGSL.Launch

namespace LeanExe.WGSL.Dispatch

def Thread.write (thread : Thread) : Option Invocation.Write :=
  match thread.state with
  | .done write => write
  | _ => none

def writes (threads : List Thread) : List Invocation.Write := threads.filterMap Thread.write

/-- Completion makes the disjoint stores visible. The list gives a canonical
order; store_commutes proves that independent store ordering is unobservable. -/
def readWrites (writes : List Invocation.Write) (initialC : WordBuffer) (address : Nat) : UInt32 :=
  match writes with
  | [] => initialC address
  | w :: rest => if address = w.address then w.value else readWrites rest initialC address

theorem readWrites_spec {list initialC address} (P : UInt32 → Prop)
    (present : ∃ w ∈ list, w.address = address)
    (all : ∀ w ∈ list, w.address = address → P w.value) :
    P (readWrites list initialC address) := by
  induction list with
  | nil => obtain ⟨w, h, _⟩ := present; cases h
  | cons w rest ih =>
      by_cases h : address = w.address
      · simpa only [readWrites, ite_eq_left h] using all w (by simp) h.symm
      · simp only [readWrites, ite_eq_right h]
        apply ih
        · obtain ⟨v, hv, ha⟩ := present
          rcases List.mem_cons.mp hv with rfl | hv
          · exact False.elim (h ha.symm)
          · exact ⟨v, hv, ha⟩
        · exact fun v hv ha => all v (List.mem_cons_of_mem _ hv) ha

theorem mem_writes {threads w} : w ∈ writes threads ↔
    ∃ thread ∈ threads, thread.state = .done (some w) := by
  simp only [writes, List.mem_filterMap]
  constructor
  · rintro ⟨t, ht, hw⟩
    refine ⟨t, ht, ?_⟩
    cases hs : t.state <;> simp [Thread.write, hs] at hw
    case done write => rw [hw]
  · rintro ⟨t, ht, hs⟩
    exact ⟨t, ht, by simp [Thread.write, hs]⟩

theorem output_corresponds {s p buffers final row col} (kernel : CheckedGemm)
    (hb : buffers.Valid kernel.ast.config)
    (run : Steps (Step s p kernel.ast.config buffers) (initial kernel.ast.config) final)
    (done : Finished final) (hr : row < kernel.ast.config.rows)
    (hc : col < kernel.ast.config.cols) (initialC : WordBuffer) :
    Dot s p kernel.ast.config buffers.a buffers.b row col kernel.ast.config.inner
      (readWrites (writes final) initialC (row * kernel.ast.config.cols + col)) := by
  obtain ⟨thread, member, w, _, hw, ha, _⟩ := completed_cell kernel hb run done hr hc
  have hi := (run.preserves kernel hb (initial_invariant s p kernel.ast.config buffers)).1
  apply readWrites_spec
  · exact ⟨w, mem_writes.mpr ⟨thread, member, hw⟩, ha⟩
  · intro v hv address
    obtain ⟨t, ht, hs⟩ := mem_writes.mp hv
    have inv := hi t ht
    rw [hs] at inv
    rw [inv.2.2.1] at address
    obtain ⟨rfl, rfl⟩ := Index.linear_injective inv.2.1 hc address
    exact inv.2.2.2

structure Input where
  buffers : Invocation.Buffers
  initialC : WordBuffer

def model (s : ScalarSemantics) : ExecutionModel CheckedGemm Input WordBuffer Invocation.Error where
  behavior p kernel input outcome :=
    let step := Step s p kernel.ast.config input.buffers
    let start := initial kernel.ast.config
    match outcome with
    | .success output => ∃ final, Steps step start final ∧ Finished final ∧
        output = readWrites (writes final) input.initialC
    | .error err => ∃ final, Steps step start final ∧
        ∃ thread ∈ final, thread.state = .error err
    | .diverges => ∃ trace : Nat → List Thread, trace 0 = start ∧
        ∀ n, step (trace n) (trace (n + 1))

def Computation (s : ScalarSemantics) (p : Profile) (config : GemmConfig)
    (input : Input) (output : WordBuffer) : Prop :=
  ∀ row col, row < config.rows → col < config.cols →
    Dot s p config input.buffers.a input.buffers.b row col config.inner
      (output (row * config.cols + col))

theorem execution {s p c} (kernel : CheckedGemm) (hc : p.scalar c)
    (he : p.evaluation .separate) (ht : ScalarTotal s c) :
    ExecutionTheorem (model s) p kernel
      (fun input => input.buffers.Valid kernel.ast.config)
      (Computation s p kernel.ast.config) where
  terminates input hb := by
    constructor
    · obtain ⟨final, run, done⟩ := launch_finishes kernel hb hc he ht
      exact ⟨_, final, run, done, rfl⟩
    · rintro ⟨trace, _, steps⟩
      exact no_infinite_steps s p kernel.ast.config input.buffers ⟨trace, steps⟩
  safe _ hb err := by
    rintro ⟨final, run, thread, member, bad⟩
    exact launch_safe kernel hb run thread member err bad
  corresponds _ _ hb run := by
    obtain ⟨final, steps, done, rfl⟩ := run
    intro row col hr hc
    exact output_corresponds kernel hb steps done hr hc _

#print axioms output_corresponds
#print axioms execution

end LeanExe.WGSL.Dispatch
