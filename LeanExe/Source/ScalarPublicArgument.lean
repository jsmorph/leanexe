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

def acceptsType : PublicArgument → Lean.Expr → Bool
  | .word, .const ``UInt64 [] => true
  | .boolean, .const ``Bool [] => true
  | _, _ => false

theorem matches_type {input : PublicArgument} {domain : Lean.Expr}
    (matched : input.acceptsType domain = true) : domain = input.type := by
  unfold acceptsType at matched
  split at matched <;> simp_all [type]

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
  | .forallE _ (.const ``UInt64 []) body _ => .word :: publicInputs body
  | .forallE _ (.const ``Bool []) body _ => .boolean :: publicInputs body
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
