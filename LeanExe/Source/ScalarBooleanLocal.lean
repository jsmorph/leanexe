import LeanExe.Source.ScalarPropositionGuard
import LeanExe.Source.ScalarBooleanProofBranch
import LeanExe.Source.ScalarBooleanLet

namespace LeanExe.Source.Scalar

/-- Bool-valued decision with exact standard proposition and decision evidence. -/
def Guard.decisionExpr (guard : Guard) : Lean.Expr :=
  .app (.app (.const ``Decidable.decide []) guard.condition) guard.evidence

/-- Standard Bool equality/inequality with the exact default instance. -/
def booleanEqualityExpr (unequal : Bool) (left right : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.const (if unequal then ``_root_.bne else ``BEq.beq) [.zero])
    (.const ``Bool []))
    (.app (.app (.const ``instBEqOfDecidableEq [.zero]) (.const ``Bool []))
      (.const ``instDecidableEqBool []))) left) right

/-- Propositional Boolean relation with its actual Eq/Ne head. -/
def booleanRelationCondition (unequal : Bool) (left right : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.const (if unequal then ``Ne else ``Eq) [.succ .zero])
    (.const ``Bool [])) left) right

theorem booleanRelationCondition_sizes (unequal : Bool) (left right : Lean.Expr) :
    sizeOf left < sizeOf (booleanRelationCondition unequal left right) ∧
      sizeOf right < sizeOf (booleanRelationCondition unequal left right) := by
  cases unequal <;> simp [booleanRelationCondition] <;> omega

def booleanRelationEvidence (unequal : Bool) (left right : Lean.Expr) : Lean.Expr :=
  let equality := .app (.app (.const ``instDecidableEqBool []) left) right
  if unequal then
    .app (.app (.const ``instDecidableNot []) (booleanRelationCondition false left right)) equality
  else equality

/-- Standard decision of Boolean equality or inequality. -/
def booleanRelationDecisionExpr (unequal : Bool) (left right : Lean.Expr) : Lean.Expr :=
  .app (.app (.const ``Decidable.decide []) (booleanRelationCondition unequal left right))
    (booleanRelationEvidence unequal left right)

def booleanRelationDecision (unequal left right : Bool) : Bool :=
  if unequal then decide (left ≠ right) else decide (left = right)

@[simp] theorem booleanRelationDecision_correct (unequal left right : Bool) :
    booleanRelationDecision unequal left right = (if unequal then left != right else left == right) := by
  cases unequal <;> cases left <;> cases right <;> rfl

/-- Boolean-valued choice over exact Boolean equality or inequality syntax. -/
def booleanChoiceExpr (unequal : Bool) (left right yes no : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) (.const ``Bool []))
    (booleanRelationCondition unequal left right))
    (booleanRelationEvidence unequal left right)) yes) no

/-- Boolean expressions with explicit lexical references, distinct from scalar operands. -/
inductive BooleanLocal where
  | var (negations index : Nat)
  | literal (negations : Nat) (value : Bool)
  | compare (op : BooleanComparison) (left right : Lean.Expr)
  | junction (negations : Nat) (op : Junction) (left right : BooleanLocal)
  | choice (negations : Nat) (unequal : Bool) (left right yes no : BooleanLocal)
  | proposition (negations : Nat) (guard : PropositionGuard) (yes no : BooleanLocal)
  | dependentChoice (negations : Nat) (shape : BooleanProofBranch) (unequal : Bool)
      (left right yes no : BooleanLocal)
  | dependentProposition (negations : Nat) (shape : BooleanProofBranch) (guard : PropositionGuard)
      (yes no : BooleanLocal)
  | binding (negations : Nat) (name : Lean.Name) (nondep : Bool) (value body : BooleanLocal)
      (type : BooleanType := .boolean)
  | wordBinding (negations : Nat) (name : Lean.Name) (nondep : Bool) (value : Lean.Expr) (body : BooleanLocal)
      (type : ResultType := .word)
  | decision (negations : Nat) (guard : PropositionGuard)
  | relationDecision (negations : Nat) (unequal : Bool) (left right : BooleanLocal)
  | equality (negations : Nat) (unequal : Bool) (left right : BooleanLocal)
  deriving Repr

namespace BooleanLocal

def expr : BooleanLocal → Lean.Expr
  | .var n index => BooleanGuardNegation.expr n (.bvar index)
  | .literal n value => BooleanGuardNegation.expr n (booleanLiteralExpr value)
  | .compare op a b => op.expr a b
  | .junction n op a b => BooleanGuardNegation.expr n (op.booleanExpr a.expr b.expr)
  | .choice n unequal a b t e => BooleanGuardNegation.expr n (booleanChoiceExpr unequal a.expr b.expr t.expr e.expr)
  | .proposition n g t e => BooleanGuardNegation.expr n (g.branch t.expr e.expr)
  | .dependentChoice n shape unequal a b t e => BooleanGuardNegation.expr n
      (shape.expr (booleanRelationCondition unequal a.expr b.expr)
        (booleanRelationEvidence unequal a.expr b.expr) t.expr e.expr)
  | .dependentProposition n shape g t e => BooleanGuardNegation.expr n
      (shape.expr g.condition g.evidence t.expr e.expr)
  | .binding n name nondep value body type => BooleanGuardNegation.expr n
      (booleanLetExpr name nondep value.expr body.expr type)
  | .wordBinding n name nondep value body type => BooleanGuardNegation.expr n
      (booleanWordLetExpr name nondep value body.expr type)
  | .decision n g => BooleanGuardNegation.expr n g.value.decisionExpr
  | .relationDecision n unequal a b => BooleanGuardNegation.expr n (booleanRelationDecisionExpr unequal a.expr b.expr)
  | .equality n unequal a b => BooleanGuardNegation.expr n (booleanEqualityExpr unequal a.expr b.expr)

def operands : BooleanLocal → List Lean.Expr
  | .var _ _ => []
  | .literal _ _ => []
  | .compare _ a b => [a, b]
  | .junction _ _ a b => a.operands ++ b.operands
  | .choice _ _ a b t e | .dependentChoice _ _ _ a b t e => a.operands ++ (b.operands ++ (t.operands ++ e.operands))
  | .proposition _ g t e | .dependentProposition _ _ g t e => g.operands ++ (t.operands ++ e.operands)
  | .binding _ name nondep value body _ => value.operands ++ body.operands.map (fun operand => booleanLetExpr name nondep value.expr operand)
  | .wordBinding _ name nondep value body _ => value :: body.operands.map (fun operand => booleanWordLetExpr name nondep value operand)
  | .decision _ g => g.operands
  | .equality _ _ a b | .relationDecision _ _ a b => a.operands ++ b.operands

def denote (native : Lean.Expr → UInt64) (booleans : Nat → Bool) : BooleanLocal → Bool
  | .var n index => GuardNegation.denote n (booleans index)
  | .literal n value => GuardNegation.denote n value
  | .compare op a b => op.denote (native a) (native b)
  | .junction n op a b => GuardNegation.denote n (op.denote (a.denote native booleans) (b.denote native booleans))
  | .choice n unequal a b t e | .dependentChoice n _ unequal a b t e => GuardNegation.denote n
      (if booleanRelationDecision unequal (a.denote native booleans) (b.denote native booleans)
       then t.denote native booleans else e.denote native booleans)
  | .proposition n g t e | .dependentProposition n _ g t e => GuardNegation.denote n
      (if g.denote native then t.denote native booleans else e.denote native booleans)
  | .binding n name nondep value body _ => GuardNegation.denote n
      (body.denote (fun operand => native (booleanLetExpr name nondep value.expr operand))
        (booleanLetBooleans (value.denote native booleans) booleans))
  | .wordBinding n name nondep value body _ => GuardNegation.denote n
      (body.denote (fun operand => native (booleanWordLetExpr name nondep value operand))
        (booleanLetBooleans false booleans))
  | .decision n g => GuardNegation.denote n (g.denote native)
  | .relationDecision n unequal a b => GuardNegation.denote n
      (booleanRelationDecision unequal (a.denote native booleans) (b.denote native booleans))
  | .equality n unequal a b => GuardNegation.denote n
      (if unequal then a.denote native booleans != b.denote native booleans
       else a.denote native booleans == b.denote native booleans)

/-- Id annotations retain syntax while Boolean binding evaluation uses the underlying type. -/
theorem binding_annotation_denote (n : Nat) (name : Lean.Name) (nondep : Bool)
    (value body : BooleanLocal) (type : BooleanType) (native : Lean.Expr → UInt64) (booleans : Nat → Bool) :
    (.binding n name nondep value body type : BooleanLocal).denote native booleans =
      (.binding n name nondep value body : BooleanLocal).denote native booleans := rfl

theorem wordBinding_annotation_denote (n : Nat) (name : Lean.Name) (nondep : Bool)
    (value : Lean.Expr) (body : BooleanLocal) (type : ResultType)
    (native : Lean.Expr → UInt64) (booleans : Nat → Bool) :
    (.wordBinding n name nondep value body type : BooleanLocal).denote native booleans =
      (.wordBinding n name nondep value body : BooleanLocal).denote native booleans := rfl

/-- The exact literal used by the usual Boolean-to-proposition truth coercion. -/
def isTrueLiteral : BooleanLocal → Bool
  | .literal 0 true => true
  | _ => false

theorem isTrueLiteral_denote {value : BooleanLocal} (native : Lean.Expr → UInt64) (booleans : Nat → Bool)
    (literal : value.isTrueLiteral = true) : value.denote native booleans = true := by
  cases value with
  | literal n flag => cases n <;> cases flag <;> simp_all [isTrueLiteral, denote, GuardNegation.denote]
  | _ => simp [isTrueLiteral] at literal

def negate : BooleanLocal → BooleanLocal
  | .var n index => .var (n + 1) index
  | .literal n value => .literal (n + 1) value
  | .compare op a b => .compare (.negate op) a b
  | .junction n op a b => .junction (n + 1) op a b
  | .choice n unequal a b t e => .choice (n + 1) unequal a b t e
  | .proposition n g t e => .proposition (n + 1) g t e
  | .dependentChoice n shape unequal a b t e => .dependentChoice (n + 1) shape unequal a b t e
  | .dependentProposition n shape g t e => .dependentProposition (n + 1) shape g t e
  | .binding n name nondep value body type => .binding (n + 1) name nondep value body type
  | .wordBinding n name nondep value body type => .wordBinding (n + 1) name nondep value body type
  | .decision n g => .decision (n + 1) g
  | .relationDecision n unequal a b => .relationDecision (n + 1) unequal a b
  | .equality n unequal a b => .equality (n + 1) unequal a b

theorem negate_expr (guard : BooleanLocal) :
    guard.negate.expr = .app (.const ``Bool.not []) guard.expr := by
  cases guard <;> rfl

theorem operands_size (guard : BooleanLocal) {operand : Lean.Expr}
    (member : operand ∈ guard.operands) : sizeOf operand < sizeOf guard.expr := by
  induction guard generalizing operand with
  | literal | var => simp [operands] at member
  | compare op a b =>
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
    have bounds := op.operands_size a b
    rcases member with rfl | rfl
    · exact bounds.1
    · exact bounds.2
  | junction n op a b iha ihb =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    cases op <;> simp only [Junction.booleanExpr]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; clear iha ihb; simp_all <;> omega)
      | (have h := ihb member; clear iha ihb; simp_all <;> omega)
  | choice n unequal a b t e iha ihb iht ihe =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    simp only [booleanChoiceExpr, booleanRelationCondition]
    rcases member with member | member | member | member
    · have h := iha member; clear iha ihb iht ihe; simp_all <;> omega
    · have h := ihb member; clear iha ihb iht ihe; simp_all <;> omega
    · have h := iht member; clear iha ihb iht ihe; simp_all <;> omega
    · have h := ihe member; clear iha ihb iht ihe; simp_all <;> omega
  | proposition n g t e iht ihe =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    simp only [PropositionGuard.branch, PropositionGuard.condition]
    rcases member with member | member | member
    · have h := g.value.operands_size member; clear iht ihe; simp_all <;> omega
    · have h := iht member; clear iht ihe; simp_all <;> omega
    · have h := ihe member; clear iht ihe; simp_all <;> omega

  | dependentChoice n shape unequal a b t e iha ihb iht ihe =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    rcases member with member | member | member | member
    · exact Nat.lt_trans (iha member) (Nat.lt_trans (booleanRelationCondition_sizes unequal a.expr b.expr).1
        (shape.condition_size _ _ _ _))
    · exact Nat.lt_trans (ihb member) (Nat.lt_trans (booleanRelationCondition_sizes unequal a.expr b.expr).2
        (shape.condition_size _ _ _ _))
    · exact Nat.lt_trans (iht member) (shape.yes_size _ _ _ _)
    · exact Nat.lt_trans (ihe member) (shape.no_size _ _ _ _)
  | dependentProposition n shape g t e iht ihe =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    rcases member with member | member | member
    · exact Nat.lt_trans (g.value.operands_size member) (shape.condition_size _ _ _ _)
    · exact Nat.lt_trans (iht member) (shape.yes_size _ _ _ _)
    · exact Nat.lt_trans (ihe member) (shape.no_size _ _ _ _)
  | binding n name nondep value body type ihv ihb =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append, List.mem_map] at member
    rcases member with member | ⟨inner, member, rfl⟩
    · have bound := ihv member
      simp only [booleanLetExpr]
      clear ihv ihb
      simp_all <;> omega
    · have bound := ihb member
      have annotationBound := BooleanType.base_size type
      simp only [BooleanType.expr] at annotationBound
      simp only [booleanLetExpr, BooleanType.expr]
      clear ihv ihb
      simp_all <;> omega
  | wordBinding n name nondep value body type ihb =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_cons, List.mem_map] at member
    rcases member with rfl | ⟨inner, innerMember, rfl⟩
    · simp [booleanWordLetExpr]
      omega
    · have bound := ihb innerMember
      have annotationBound := ResultType.word_size type
      simp only [ResultType.expr] at annotationBound
      clear ihb
      simp only [booleanWordLetExpr, ResultType.expr]
      simp_all <;> omega
  | decision n g =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    have bound := g.value.operands_size member
    simp only [Guard.decisionExpr]
    simp_all
    omega

  | equality n unequal a b iha ihb =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    cases unequal <;> simp only [booleanEqualityExpr]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; clear iha ihb; simp_all <;> omega)
      | (have h := ihb member; clear iha ihb; simp_all <;> omega)
  | relationDecision n unequal a b iha ihb =>
    apply Nat.lt_of_lt_of_le _ (BooleanGuardNegation.expr_size n _)
    simp only [operands, List.mem_append] at member
    cases unequal <;> simp only [booleanRelationDecisionExpr, booleanRelationCondition]
    all_goals rcases member with member | member
    all_goals first
      | (have h := iha member; clear iha ihb; simp_all <;> omega)
      | (have h := ihb member; clear iha ihb; simp_all <;> omega)

def variables : BooleanLocal → List Nat
  | .var _ index => [index]
  | .literal .. | .compare .. | .decision .. => []
  | .junction _ _ a b => a.variables ++ b.variables
  | .choice _ _ a b t e | .dependentChoice _ _ _ a b t e => a.variables ++ (b.variables ++ (t.variables ++ e.variables))
  | .proposition _ _ t e | .dependentProposition _ _ _ t e => t.variables ++ e.variables
  | .equality _ _ a b | .relationDecision _ _ a b => a.variables ++ b.variables
  | .binding _ _ _ value body _ => value.variables ++ booleanLetVariables body.variables
  | .wordBinding _ _ _ _ body _ => booleanLetVariables body.variables

/-- Word-bound slots cannot be used as Boolean references, including in nested values. -/
def WellScoped : BooleanLocal → Prop
  | .var .. | .literal .. | .compare .. | .decision .. => True
  | .junction _ _ a b | .equality _ _ a b | .relationDecision _ _ a b
  | .binding _ _ _ a b _ => a.WellScoped ∧ b.WellScoped
  | .choice _ _ a b t e | .dependentChoice _ _ _ a b t e =>
      a.WellScoped ∧ b.WellScoped ∧ t.WellScoped ∧ e.WellScoped
  | .proposition _ _ t e | .dependentProposition _ _ _ t e => t.WellScoped ∧ e.WellScoped
  | .wordBinding _ _ _ _ body _ => 0 ∉ body.variables ∧ body.WellScoped

/-- Whether this value needs the Boolean-local path beyond the closed guard grammar. -/
def extended : BooleanLocal → Bool
  | .var .. | .choice .. | .proposition .. | .dependentChoice .. | .dependentProposition ..
  | .decision .. | .equality .. | .relationDecision .. | .binding .. | .wordBinding .. => true
  | .literal .. | .compare .. => false
  | .junction _ _ a b => a.extended || b.extended

def condition (value : BooleanLocal) : Lean.Expr :=
  .app (.app (.app (.const ``Eq [.succ .zero]) (.const ``Bool [])) value.expr) (.const ``Bool.true [])

def evidence (value : BooleanLocal) : Lean.Expr :=
  .app (.app (.const ``instDecidableEqBool []) value.expr) (.const ``Bool.true [])

end BooleanLocal
/-- Surface proposition paired with the Boolean value that it decides.
Eq with a literal true right side retains the existing truth-condition path. -/
inductive BooleanConditionForm : BooleanLocal → Type where
  | truth (value : BooleanLocal) : BooleanConditionForm value
  | equal (left right : BooleanLocal) (nontrue : right.expr ≠ .const ``Bool.true []) :
      BooleanConditionForm (.equality 0 false left right)
  | unequal (left right : BooleanLocal) : BooleanConditionForm (.equality 0 true left right)

namespace BooleanConditionForm

def condition : {value : BooleanLocal} → BooleanConditionForm value → Lean.Expr
  | _, .truth value => value.condition
  | _, .equal left right _ => booleanRelationCondition false left.expr right.expr
  | _, .unequal left right => booleanRelationCondition true left.expr right.expr

def evidence : {value : BooleanLocal} → BooleanConditionForm value → Lean.Expr
  | _, .truth value => value.evidence
  | _, .equal left right _ => booleanRelationEvidence false left.expr right.expr
  | _, .unequal left right => booleanRelationEvidence true left.expr right.expr

theorem operands_size {value : BooleanLocal} (form : BooleanConditionForm value)
    {operand : Lean.Expr} (member : operand ∈ value.operands) :
    sizeOf operand < sizeOf form.condition := by
  cases form with
  | truth value =>
    have bound := value.operands_size member
    simp only [condition, BooleanLocal.condition]
    simp_all
    omega
  | equal left right nontrue =>
    change operand ∈ left.operands ++ right.operands at member
    rcases List.mem_append.mp member with member | member
    · have bound := left.operands_size member
      simp only [condition, booleanRelationCondition]
      simp_all
      omega
    · have bound := right.operands_size member
      simp only [condition, booleanRelationCondition]
      simp_all
      omega
  | unequal left right =>
    change operand ∈ left.operands ++ right.operands at member
    rcases List.mem_append.mp member with member | member
    · have bound := left.operands_size member
      simp only [condition, booleanRelationCondition]
      simp_all
      omega
    · have bound := right.operands_size member
      simp only [condition, booleanRelationCondition]
      simp_all
      omega

end BooleanConditionForm

/-- A condition using Boolean bindings or Boolean-valued choices. The preceding
closed guard forms retain their existing source and compiler paths. -/
structure BooleanLocalGuard where
  value : BooleanLocal
  expanded : value.extended = true
  form : BooleanConditionForm value := .truth value

namespace BooleanLocalGuard
abbrev condition (guard : BooleanLocalGuard) := guard.form.condition
abbrev evidence (guard : BooleanLocalGuard) := guard.form.evidence

theorem operands_size (guard : BooleanLocalGuard) {operand : Lean.Expr}
    (member : operand ∈ guard.value.operands) : sizeOf operand < sizeOf guard.condition :=
  guard.form.operands_size member

def branch (guard : BooleanLocalGuard) (type t e : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``ite [.succ .zero]) type)
    guard.condition) guard.evidence) t) e
def dependentBranch (guard : BooleanLocalGuard) (type : Lean.Expr)
    (tn fn : Lean.Name) (tb fb : Lean.BinderInfo) (t e : Lean.Expr) : Lean.Expr :=
  .app (.app (.app (.app (.app (.const ``dite [.succ .zero]) type)
    guard.condition) guard.evidence)
      (.lam tn guard.condition t tb))
      (.lam fn (.app (.const ``Not []) guard.condition) e fb)

end BooleanLocalGuard

end LeanExe.Source.Scalar
