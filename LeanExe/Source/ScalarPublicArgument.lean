import LeanExe.Source.ScalarValues

namespace LeanExe.Source.Scalar

/-- Public scalar argument kinds. Boolean inputs use nonzero i64 values for true. -/
inductive PublicArgument where
  | word
  | boolean
  deriving DecidableEq, Repr

namespace PublicArgument

def type : PublicArgument → Lean.Expr
  | .word => .const ``UInt64 []
  | .boolean => .const ``Bool []

/-- Parameter annotations preserve the base scalar representation. -/
inductive Domain : PublicArgument → Lean.Expr → Prop where
  | word : Domain .word (.const ``UInt64 [])
  | boolean : Domain .boolean (.const ``Bool [])
  | identity (inner : Domain input domain) :
      Domain input (.app (.const ``Id [.zero]) domain)

def ofType? : Lean.Expr → Option PublicArgument
  | .const ``UInt64 [] => some .word
  | .const ``Bool [] => some .boolean
  | .app (.const ``Id [.zero]) inner => ofType? inner
  | _ => none

theorem ofType_accepts {input : PublicArgument} {domain : Lean.Expr}
    (valid : Domain input domain) : ofType? domain = some input := by
  induction valid with
  | word => rfl
  | boolean => rfl
  | identity _ ih => exact ih

theorem ofType_sound {input : PublicArgument} {domain : Lean.Expr}
    (parsed : ofType? domain = some input) : Domain input domain := by
  fun_induction ofType? domain with
  | case1 => cases Option.some.inj parsed; exact .word
  | case2 => cases Option.some.inj parsed; exact .boolean
  | case3 inner ih => exact .identity (ih parsed)
  | case4 => contradiction

def acceptsType (input : PublicArgument) (domain : Lean.Expr) : Bool :=
  decide (ofType? domain = some input)

theorem acceptsType_domain {input : PublicArgument} {domain : Lean.Expr}
    (matched : input.acceptsType domain = true) : Domain input domain :=
  ofType_sound (of_decide_eq_true matched)

def kind : PublicArgument → BindingKind
  | .word => .word
  | .boolean => .boolean

def decode : PublicArgument → UInt64 → Value
  | .word, value => .word value
  | .boolean, value => .boolean (value != 0)

@[simp] theorem decode_kind (argument : PublicArgument) (value : UInt64) :
    (argument.decode value).kind = argument.kind := by
  cases argument <;> rfl

end PublicArgument

/-- Input order from the original declared signature. Result annotations contain
no public inputs. Signature admission independently checks the whole type. -/
def publicInputs : Lean.Expr → List PublicArgument
  | .forallE _ domain body _ =>
      match PublicArgument.ofType? domain with
      | some input => input :: publicInputs body
      | none => []
  | .mdata _ body => publicInputs body
  | _ => []

/-- Public lambda annotations agree with the independently declared input kinds. -/
def publicLambdasMatch : List PublicArgument → Lean.Expr → Bool
  | [], _ => true
  | input :: inputs, source =>
      match source.consumeMData with
      | .lam _ domain body _ => input.acceptsType domain && publicLambdasMatch inputs body
      | _ => false

def publicValues (inputs : List PublicArgument) (args : List UInt64) : List Value :=
  List.zipWith PublicArgument.decode inputs args

theorem publicValues_typed {inputs : List PublicArgument} {args : List UInt64}
    (len : args.length = inputs.length) :
    (publicValues inputs args).map Value.kind = inputs.map PublicArgument.kind := by
  induction inputs generalizing args with
  | nil => cases args <;> simp_all [publicValues]
  | cons input inputs ih =>
    cases args with
    | nil => simp at len
    | cons arg args =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at len
      simpa [publicValues] using congrArg (List.cons input.kind) (ih len)

theorem publicValues_words (args : List UInt64) :
    publicValues (List.replicate args.length .word) args = args.map Value.word := by
  induction args with
  | nil => rfl
  | cons arg args ih => simpa [publicValues, List.replicate_succ, PublicArgument.decode] using congrArg (List.cons (.word arg)) ih

end LeanExe.Source.Scalar
