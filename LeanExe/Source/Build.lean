import LeanExe.Source.Syntax

/-!
The build kernels that the GPU targets translate: for each index below the count, the value of the
expression `element` after the statements `body`, with the index in local `index` and the count a
`u64` parameter or the length of an array parameter.  `Spec.locals` and `Spec.arrays` give the
source locals and arrays of an index, and `Spec.WF` and `Spec.Fits` state the conditions on a
kernel's indices and on its arguments that the translations' theorems assume.
-/

namespace LeanExe.Source

inductive Kind where
  | word
  | float
  | array
  deriving DecidableEq, Repr

/-- An argument of a kernel. -/
inductive Arg where
  | word (value : UInt64)
  | float (bits : UInt32)
  | array (xs : Array UInt64)

def Arg.kind : Arg → Kind
  | .word _ => .word
  | .float _ => .float
  | .array _ => .array

/-- Where a build kernel's count comes from: the length of array parameter `src`, which local
`sizeLocal` holds, or `u64` parameter `j`. -/
inductive Count where
  | size (sizeLocal src : Nat)
  | param (j : Nat)

def Count.sizeLocal? : Count → Option Nat
  | .size l _ => some l
  | .param _ => none

/-- A build kernel: the parameters' kinds, the build's index local, the count, the locals that
the per-element statements assign with their types, a bound on the source locals, the per-element
statements, and the element. -/
structure Spec where
  kinds : List Kind
  index : Nat
  count : Count
  vars : List (Nat × Source.ScalarType)
  width : Nat
  body : Source.Stmt
  element : Source.Expr .u64

/-- The source locals that the statements' denotation reads at index `k` with count `n`. -/
def Spec.locals (K : Spec) (args : List Arg) (k n : Nat) (j : Nat) : Option Wasm.Value :=
  if j = K.index then some (.i64 (UInt64.ofNat k))
  else if K.count.sizeLocal? = some j then some (.i64 (UInt64.ofNat n))
  else match args[j]? with
    | some (.word v) => some (.i64 v)
    | some (.float bits) => some (.f32 bits)
    | _ => none

def Spec.arrays (args : List Arg) (a : Nat) : Option (Array UInt64) :=
  match args[a]? with
  | some (.array xs) => some xs
  | _ => none

/-- The conditions on a kernel's own indices, checked by evaluation. -/
def Spec.wfb (K : Spec) : Bool :=
  decide (K.kinds.length ≤ K.index) && decide (K.index < K.width) &&
  decide (K.kinds.length ≤ K.width) &&
  (match K.count with
    | .size l src => decide (K.kinds.length ≤ l) && decide (l < K.width) && decide (l ≠ K.index) &&
        decide (K.kinds[src]? = some .array)
    | .param j => decide (K.kinds[j]? = some .word)) &&
  decide (K.vars.map (·.1)).Nodup &&
  K.vars.all fun (j, _) => decide (K.kinds.length ≤ j) && decide (j < K.width) &&
    decide (j ≠ K.index) && decide (K.count.sizeLocal? ≠ some j)

/-- The conditions a kernel's arguments satisfy, with count `n`. -/
structure Spec.Fits (K : Spec) (args : List Arg) (n : Nat) : Prop where
  kinds : args.map Arg.kind = K.kinds
  sizes : ∀ ys, Arg.array ys ∈ args → ys.size < 2 ^ 29
  count : match K.count with
    | .size _ src => ∃ xs, args[src]? = some (.array xs) ∧ xs.size = n
    | .param j => args[j]? = some (.word (UInt64.ofNat n))
  bound : n < 2 ^ 29

/-- The facts that `Spec.wfb` checks. -/
structure Spec.WF (K : Spec) : Prop where
  index : K.kinds.length ≤ K.index
  indexW : K.index < K.width
  kindsW : K.kinds.length ≤ K.width
  count : match K.count with
    | .size l src => K.kinds.length ≤ l ∧ l < K.width ∧ l ≠ K.index ∧ K.kinds[src]? = some .array
    | .param j => K.kinds[j]? = some .word
  nodup : (K.vars.map (·.1)).Nodup
  vars : ∀ j type, (j, type) ∈ K.vars → K.kinds.length ≤ j ∧ j < K.width ∧ j ≠ K.index ∧
    K.count.sizeLocal? ≠ some j

theorem Spec.wf_of_wfb (K : Spec) (h : K.wfb = true) : K.WF := by
  simp only [Spec.wfb, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  refine ⟨h1, h2, h3, ?_, h5, fun j type hj => ?_⟩
  · cases hc : K.count <;> simp_all
  · have h' := h6 (j, type) hj
    exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

theorem lookup_mem {vars : List (Nat × Source.ScalarType)} {j : Nat}
    {type : Source.ScalarType} (h : vars.lookup j = some type) : (j, type) ∈ vars := by
  induction vars with
  | nil => simp at h
  | cons x vars ih =>
      obtain ⟨a, t⟩ := x
      by_cases ha : j = a
      · subst ha
        simp only [List.lookup_cons, BEq.rfl, Option.some.injEq] at h
        subst h
        simp
      · simp only [List.lookup_cons, show (j == a) = false by simpa using ha] at h
        exact List.mem_cons_of_mem _ (ih h)

theorem lookup_of_mem {vars : List (Nat × Source.ScalarType)} (hnd : (vars.map (·.1)).Nodup)
    {j : Nat} {type : Source.ScalarType} (h : (j, type) ∈ vars) : vars.lookup j = some type := by
  induction vars with
  | nil => cases h
  | cons x vars ih =>
      obtain ⟨a, t⟩ := x
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp
      · have hne : j ≠ a := fun hj => hnd.1 ⟨(j, type), h, by simp [hj]⟩
        simp only [List.lookup_cons, show (j == a) = false by simpa using hne]
        exact ih hnd.2 h

end LeanExe.Source
