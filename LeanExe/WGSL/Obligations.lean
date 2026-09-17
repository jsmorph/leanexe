import LeanExe.WGSL.Profile

namespace LeanExe.WGSL

/-- Outcomes retain dynamic errors and nontermination instead of defining them
    away by quantifying only over successful executions. -/
inductive Outcome (Output Error : Type) where
  | success : Output → Outcome Output Error
  | error : Error → Outcome Output Error
  | diverges : Outcome Output Error

/-- Interface to a shared execution semantics, later instantiated by the parsed
    subset. The interface itself asserts no correctness of a kernel or runtime. -/
structure ExecutionModel (Kernel Input Output Error : Type) where
  behavior : Profile → Kernel → Input → Outcome Output Error → Prop

def ExecutionModel.Exec {K I O E} (m : ExecutionModel K I O E)
    (p : Profile) (k : K) (i : I) (o : O) : Prop :=
  m.behavior p k i (.success o)

def ExecutionModel.Terminates {K I O E} (m : ExecutionModel K I O E)
    (p : Profile) (k : K) (i : I) : Prop :=
  (∃ o, m.Exec p k i o) ∧ ¬ m.behavior p k i .diverges

def ExecutionModel.Safe {K I O E} (m : ExecutionModel K I O E)
    (p : Profile) (k : K) (i : I) : Prop :=
  ∀ err, ¬ m.behavior p k i (.error err)

/-- A total execution theorem must establish existence, termination, safety,
    and output correspondence. Scheduling and resources belong in `domain`. -/
structure ExecutionTheorem {K I O E} (m : ExecutionModel K I O E)
    (p : Profile) (k : K) (domain : I → Prop) (computation : I → O → Prop) : Prop where
  terminates : ∀ i, domain i → m.Terminates p k i
  safe : ∀ i, domain i → m.Safe p k i
  corresponds : ∀ i o, domain i → m.Exec p k i o → computation i o

theorem ExecutionTheorem.numerical {K I O E} {m : ExecutionModel K I O E}
    {p k domain computation} (h : ExecutionTheorem m p k domain computation)
    (bound : I → O → Prop)
    (numerical : ∀ i o, domain i → computation i o → bound i o) :
    ∀ i o, domain i → m.Exec p k i o → bound i o :=
  fun i o hi ho => numerical i o hi (h.corresponds i o hi ho)

/-- Exactness is additional to the total execution theorem. Bit-level equality
    follows when the output type records words, including signed-zero bits. -/
def Exact {I O} (computation : I → O → Prop) (reference : I → O) : Prop :=
  ∀ i o, computation i o → o = reference i

theorem ExecutionTheorem.exact {K I O E} {m : ExecutionModel K I O E}
    {p k domain computation} (h : ExecutionTheorem m p k domain computation)
    {reference : I → O} (he : Exact computation reference) :
    ∀ i o, domain i → m.Exec p k i o → o = reference i :=
  fun i o hi ho => he i o (h.corresponds i o hi ho)

end LeanExe.WGSL
