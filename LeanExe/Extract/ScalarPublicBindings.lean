import LeanExe.Source.ScalarPublicArgument
import LeanExe.Extract.ScalarBindings
import LeanExe.Extract.ScalarGuardLowering

namespace LeanExe.Extract.Core
open LeanExe.Source.Scalar

def publicBinding (argument : PublicArgument) (slot : Nat) : ScalarBinding :=
  match argument with
  | .word => .word (.local slot)
  | .boolean => .boolean (guardWord (lowerComparison .bne (.local slot) (.u64 0)))

def publicBindingsFor (inputs : List PublicArgument) (slots : List Nat) : List ScalarBinding :=
  List.zipWith publicBinding inputs slots

/-- Source de Bruijn order, with Boolean input words normalized before use. -/
def publicBindings (inputs : List PublicArgument) : List ScalarBinding :=
  publicBindingsFor inputs.reverse (List.range inputs.length).reverse

@[simp] theorem publicBinding_kind (input : PublicArgument) (slot : Nat) :
    (publicBinding input slot).kind = input.kind := by
  cases input <;> rfl

theorem publicBindingsFor_typed {inputs : List PublicArgument} {slots : List Nat}
    (len : slots.length = inputs.length) :
    (publicBindingsFor inputs slots).map ScalarBinding.kind = inputs.map PublicArgument.kind := by
  induction inputs generalizing slots with
  | nil => cases slots <;> simp_all [publicBindingsFor]
  | cons input inputs ih =>
    cases slots with
    | nil => simp at len
    | cons slot slots =>
      have tail : slots.length = inputs.length := by simpa using len
      simpa [publicBindingsFor] using congrArg (List.cons input.kind) (ih tail)

@[simp] theorem publicBindings_typed (inputs : List PublicArgument) :
    (publicBindings inputs).map ScalarBinding.kind = inputs.reverse.map PublicArgument.kind :=
  publicBindingsFor_typed (by simp)

theorem publicValues_bindings_typed {inputs : List PublicArgument} {args : List UInt64}
    (len : args.length = inputs.length) :
    (publicValues inputs args).reverse.map Value.kind = (publicBindings inputs).map ScalarBinding.kind := by
  rw [List.map_reverse, publicValues_typed len, publicBindings_typed, List.map_reverse]

theorem publicBindingsFor_words (slots : List Nat) :
    publicBindingsFor (List.replicate slots.length .word) slots =
      slots.map (fun slot => ScalarBinding.word (.local slot)) := by
  induction slots with
  | nil => rfl
  | cons slot slots ih =>
    simpa [publicBindingsFor, List.replicate_succ, publicBinding] using
      congrArg (List.cons (.word (.local slot))) ih

@[simp] theorem publicBindings_words (arity : Nat) :
    publicBindings (List.replicate arity .word) =
      (List.range arity).reverse.map (fun slot => ScalarBinding.word (.local slot)) := by
  simpa [publicBindings] using publicBindingsFor_words (List.range arity).reverse

theorem publicBindingsFor_total (inputs : List PublicArgument) (slots : List Nat) :
    ∀ binding ∈ publicBindingsFor inputs slots, binding.Total := by
  induction inputs generalizing slots with
  | nil => simp [publicBindingsFor]
  | cons input inputs ih =>
    cases slots with
    | nil => simp [publicBindingsFor]
    | cons slot slots =>
      intro binding member
      change binding ∈ publicBinding input slot :: publicBindingsFor inputs slots at member
      rcases List.mem_cons.mp member with rfl | member
      · cases input <;> trivial
      · exact ih slots _ member

theorem publicBindings_total (inputs : List PublicArgument) :
    ∀ binding ∈ publicBindings inputs, binding.Total :=
  publicBindingsFor_total _ _

theorem publicBinding_matches {store : LeanExe.IR.ScalarStore} {slot : Nat} {value : UInt64}
    (input : PublicArgument) (read : store[slot]? = some value) :
    (publicBinding input slot).Matches store (input.decode value) := by
  cases input with
  | word => exact .local read
  | boolean => exact guardWord_correct (lowerComparison_correct .bne (.local read) .const)

theorem publicBindingsFor_matches (inputs : List PublicArgument) (slots : List Nat)
    (args : List UInt64) (store : LeanExe.IR.ScalarStore)
    (matched : ∀ (index slot : Nat) (value : UInt64), slots[index]? = some slot → args[index]? = some value →
      store[slot]? = some value) :
    ScalarBindingsMatch (publicBindingsFor inputs slots) (publicValues inputs args) store := by
  induction inputs generalizing slots args with
  | nil => intro index binding value found; simp [publicBindingsFor] at found
  | cons input inputs ih =>
    cases slots with
    | nil => intro index binding value found; simp [publicBindingsFor] at found
    | cons slot slots =>
      cases args with
      | nil => intro index binding value _ found; simp [publicValues] at found
      | cons arg args =>
        apply ScalarBindingsMatch.cons
        · exact ih slots args (fun index slot value hs hv => matched (index + 1) slot value hs hv)
        · exact publicBinding_matches input (matched 0 slot arg rfl rfl)

/-- Argument normalization preserves every scalar invariant closed under
constants and comparison choices. -/
theorem publicBindingsFor_holds (P : LeanExe.IR.Expr → Prop)
    (literal : ∀ n, P (.u64 n))
    (choice : ∀ op a b t e, P a → P b → P t → P e → P (.ite (lowerComparison op a b) t e))
    (inputs : List PublicArgument) (slots : List Nat)
    (reads : ∀ slot ∈ slots, P (.local slot)) :
    ∀ binding ∈ publicBindingsFor inputs slots, binding.Holds P := by
  induction inputs generalizing slots with
  | nil => simp [publicBindingsFor]
  | cons input inputs ih =>
    cases slots with
    | nil => simp [publicBindingsFor]
    | cons slot slots =>
      intro binding member
      change binding ∈ publicBinding input slot :: publicBindingsFor inputs slots at member
      rcases List.mem_cons.mp member with rfl | member
      · cases input with
        | word => exact reads slot (by simp)
        | boolean =>
          exact choice .bne (.local slot) (.u64 0) (.u64 1) (.u64 0)
            (reads slot (by simp)) (literal 0) (literal 1) (literal 0)
      · exact ih slots (fun index member => reads index (by simp [member])) _ member

end LeanExe.Extract.Core
