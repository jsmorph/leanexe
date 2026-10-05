/-! Allocation-free specifications for first-method lookup and live-home unwinding.
These are control laws, not a refinement theorem for the concrete heap or WASM. -/
namespace LeanExe.Smalltalk.Control

structure Method where
  owner : Nat
  selector : Nat
  body : Nat
  deriving DecidableEq, Repr
def own : List Method → Nat → Nat → Option Method
  | [], _, _ => none
  | m :: ms, c, s => if m.owner = c ∧ m.selector = s then some m else own ms c s
inductive First : List Method → Nat → Nat → Method → Prop
  | here (h : m.owner = c ∧ m.selector = s) : First (m :: ms) c s m
  | there (h : ¬(a.owner = c ∧ a.selector = s)) (rest : First ms c s m) : First (a :: ms) c s m
def parent (classes : List (Nat × Nat)) (c : Nat) : Nat := (classes.lookup c).getD 0
def resolve (classes : List (Nat × Nat)) (methods : List Method) : Nat → Nat → Nat → Option Method
  | 0, _, _ => none
  | fuel + 1, c, s => if c = 0 then none else
    match own methods c s with
    | some m => some m
    | none => resolve classes methods fuel (parent classes c) s
inductive Resolves (classes : List (Nat × Nat)) (methods : List Method) : Nat → Nat → Nat → Method → Prop
  | here (live : c ≠ 0) (first : First methods c s m) : Resolves classes methods (fuel + 1) c s m
  | up (live : c ≠ 0) (absent : own methods c s = none)
      (rest : Resolves classes methods fuel (parent classes c) s m) :
      Resolves classes methods (fuel + 1) c s m

structure Activation where
  id : Nat
  lexicalHome : Nat
  live : Bool
  slots : List Nat
  operands : List Nat
  deriving DecidableEq, Repr
def retire (a : Activation) : Activation := {a with live := false, operands := []}
def unwind (target : Nat) : List Activation → Option (List Activation × List Activation)
  | [] => none
  | a :: rest => if a.live then
      if a.id = target then some ([retire a], rest)
      else match unwind target rest with
        | none => none
        | some (retired, tail) => some (retire a :: retired, tail)
    else none
inductive Unwinds (target : Nat) : List Activation → List Activation → List Activation → Prop
  | here (live : a.live = true) (same : a.id = target) : Unwinds target (a :: rest) [retire a] rest
  | next (live : a.live = true) (different : a.id ≠ target)
      (rest : Unwinds target chain retired tail) :
      Unwinds target (a :: chain) (retire a :: retired) tail

end LeanExe.Smalltalk.Control
