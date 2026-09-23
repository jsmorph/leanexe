import Std

/-!
# Formation of first-order nominal declarations

Nominal references are finite table indices. Formation checks reference bounds,
without unfolding declarations, so arbitrary mutual recursion is permitted.
All type constructors are strictly positive: this grammar has no function type.
A declaration may have no constructors, and a constructor may have no fields.
Formation does not assert inhabitation or termination.
-/

namespace LeanExe.TypeSafety

/-- Supported word widths are explicit, finite, and nonzero. -/
inductive WordWidth where
  | w8 | w32 | w64
  deriving DecidableEq, Repr

def WordWidth.bits : WordWidth → Nat
  | .w8 => 8
  | .w32 => 32
  | .w64 => 64

def WordWidth.modulus (width : WordWidth) : Nat := 2 ^ width.bits

theorem WordWidth.modulus_pos (width : WordWidth) : 0 < width.modulus := by
  cases width <;> decide

theorem WordWidth.modulus_mono {source target : WordWidth} (ordered : source.bits ≤ target.bits) :
    source.modulus ≤ target.modulus := by
  exact Nat.pow_le_pow_right Nat.zero_lt_two ordered

inductive Ty where
  | unit
  | bool
  | nat64
  | word (width : WordWidth)
  | prod (left right : Ty)
  | sum (left right : Ty)
  | array (item : Ty)
  | data (index : Nat)
  deriving DecidableEq, Repr

/-- Constructor order determines tags; each constructor lists its field types. -/
abbrev DataDecl := List (List Ty)
abbrev DataDecls := List DataDecl
abbrev Context := List Ty

structure Signature where
  params : List Ty
  result : Ty
  deriving Repr

abbrev Signatures := List Signature

/-- Total indexed lookup, also used by the independent runtime machine. -/
def lookup {α : Type} : List α → Nat → Option α
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs, n + 1 => lookup xs n

theorem lookup_lt (found : lookup xs index = some value) : index < xs.length := by
  induction xs generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => exact Nat.zero_lt_succ _
      | succ index => exact Nat.succ_lt_succ (ih found)

inductive TyWF (declarations : DataDecls) : Ty → Prop where
  | unit : TyWF declarations .unit
  | bool : TyWF declarations .bool
  | nat64 : TyWF declarations .nat64
  | word : TyWF declarations (.word width)
  | prod : TyWF declarations α → TyWF declarations β → TyWF declarations (.prod α β)
  | sum : TyWF declarations α → TyWF declarations β → TyWF declarations (.sum α β)
  | array : TyWF declarations α → TyWF declarations (.array α)
  | data : index < declarations.length → TyWF declarations (.data index)

inductive TypesWF (declarations : DataDecls) : List Ty → Prop where
  | nil : TypesWF declarations []
  | cons : TyWF declarations α → TypesWF declarations rest → TypesWF declarations (α :: rest)

inductive ConstructorsWF (declarations : DataDecls) : DataDecl → Prop where
  | nil : ConstructorsWF declarations []
  | cons : TypesWF declarations fields → ConstructorsWF declarations rest →
      ConstructorsWF declarations (fields :: rest)

inductive DeclarationTableWF (declarations : DataDecls) : DataDecls → Prop where
  | nil : DeclarationTableWF declarations []
  | cons : ConstructorsWF declarations constructors → DeclarationTableWF declarations rest →
      DeclarationTableWF declarations (constructors :: rest)

abbrev DeclarationsWF (declarations : DataDecls) : Prop :=
  DeclarationTableWF declarations declarations

structure SignatureWF (declarations : DataDecls) (signature : Signature) : Prop where
  params : TypesWF declarations signature.params
  result : TyWF declarations signature.result

inductive SignaturesWF (declarations : DataDecls) : Signatures → Prop where
  | nil : SignaturesWF declarations []
  | cons : SignatureWF declarations signature → SignaturesWF declarations rest →
      SignaturesWF declarations (signature :: rest)

def tyWellFormed (declarations : DataDecls) : Ty → Bool
  | .unit | .bool | .nat64 | .word _ => true
  | .prod α β | .sum α β => tyWellFormed declarations α && tyWellFormed declarations β
  | .array α => tyWellFormed declarations α
  | .data index => decide (index < declarations.length)

def typesWellFormed (declarations : DataDecls) : List Ty → Bool
  | [] => true
  | α :: rest => tyWellFormed declarations α && typesWellFormed declarations rest

def constructorsWellFormed (declarations : DataDecls) : DataDecl → Bool
  | [] => true
  | fields :: rest => typesWellFormed declarations fields && constructorsWellFormed declarations rest

def declarationTableWellFormed (declarations : DataDecls) : DataDecls → Bool
  | [] => true
  | constructors :: rest =>
      constructorsWellFormed declarations constructors && declarationTableWellFormed declarations rest

def declarationsWellFormed (declarations : DataDecls) : Bool :=
  declarationTableWellFormed declarations declarations

def signatureWellFormed (declarations : DataDecls) (signature : Signature) : Bool :=
  typesWellFormed declarations signature.params && tyWellFormed declarations signature.result

def signaturesWellFormed (declarations : DataDecls) : Signatures → Bool
  | [] => true
  | signature :: rest =>
      signatureWellFormed declarations signature && signaturesWellFormed declarations rest

theorem tyWellFormed_iff : tyWellFormed declarations τ = true ↔ TyWF declarations τ := by
  induction τ with
  | unit => exact ⟨fun _ => .unit, fun _ => rfl⟩
  | bool => exact ⟨fun _ => .bool, fun _ => rfl⟩
  | nat64 => exact ⟨fun _ => .nat64, fun _ => rfl⟩
  | word _ => exact ⟨fun _ => .word, fun _ => rfl⟩
  | prod α β ihα ihβ =>
      constructor
      · intro checked
        obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp checked
        exact .prod (ihα.mp left) (ihβ.mp right)
      · intro formed
        cases formed with
        | prod left right => exact Bool.and_eq_true_iff.mpr ⟨ihα.mpr left, ihβ.mpr right⟩
  | sum α β ihα ihβ =>
      constructor
      · intro checked
        obtain ⟨left, right⟩ := Bool.and_eq_true_iff.mp checked
        exact .sum (ihα.mp left) (ihβ.mp right)
      · intro formed
        cases formed with
        | sum left right => exact Bool.and_eq_true_iff.mpr ⟨ihα.mpr left, ihβ.mpr right⟩
  | array α ih =>
      constructor
      · exact fun checked => .array (ih.mp checked)
      · intro formed
        cases formed with
        | array item => exact ih.mpr item
  | data index =>
      constructor
      · exact fun checked => .data (of_decide_eq_true checked)
      · intro formed
        cases formed with
        | data bounded => exact decide_eq_true bounded

theorem typesWellFormed_iff :
    typesWellFormed declarations types = true ↔ TypesWF declarations types := by
  induction types with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons α rest ih =>
      constructor
      · intro checked
        obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp checked
        exact .cons (tyWellFormed_iff.mp head) (ih.mp tail)
      · intro formed
        cases formed with
        | cons head tail =>
            exact Bool.and_eq_true_iff.mpr ⟨tyWellFormed_iff.mpr head, ih.mpr tail⟩

theorem constructorsWellFormed_iff :
    constructorsWellFormed declarations constructors = true ↔
      ConstructorsWF declarations constructors := by
  induction constructors with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons fields rest ih =>
      constructor
      · intro checked
        obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp checked
        exact .cons (typesWellFormed_iff.mp head) (ih.mp tail)
      · intro formed
        cases formed with
        | cons head tail =>
            exact Bool.and_eq_true_iff.mpr ⟨typesWellFormed_iff.mpr head, ih.mpr tail⟩

theorem declarationTableWellFormed_iff :
    declarationTableWellFormed declarations table = true ↔ DeclarationTableWF declarations table := by
  induction table with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons constructors rest ih =>
      constructor
      · intro checked
        obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp checked
        exact .cons (constructorsWellFormed_iff.mp head) (ih.mp tail)
      · intro formed
        cases formed with
        | cons head tail =>
            exact Bool.and_eq_true_iff.mpr ⟨constructorsWellFormed_iff.mpr head, ih.mpr tail⟩

theorem declarationsWellFormed_iff :
    declarationsWellFormed declarations = true ↔ DeclarationsWF declarations :=
  declarationTableWellFormed_iff

theorem signatureWellFormed_iff :
    signatureWellFormed declarations signature = true ↔ SignatureWF declarations signature := by
  constructor
  · intro checked
    obtain ⟨params, result⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨typesWellFormed_iff.mp params, tyWellFormed_iff.mp result⟩
  · intro formed
    exact Bool.and_eq_true_iff.mpr
      ⟨typesWellFormed_iff.mpr formed.params, tyWellFormed_iff.mpr formed.result⟩

theorem signaturesWellFormed_iff :
    signaturesWellFormed declarations signatures = true ↔ SignaturesWF declarations signatures := by
  induction signatures with
  | nil => exact ⟨fun _ => .nil, fun _ => rfl⟩
  | cons signature rest ih =>
      constructor
      · intro checked
        obtain ⟨head, tail⟩ := Bool.and_eq_true_iff.mp checked
        exact .cons (signatureWellFormed_iff.mp head) (ih.mp tail)
      · intro formed
        cases formed with
        | cons head tail =>
            exact Bool.and_eq_true_iff.mpr ⟨signatureWellFormed_iff.mpr head, ih.mpr tail⟩

theorem TypesWF.append (left : TypesWF declarations Γ) (right : TypesWF declarations Δ) :
    TypesWF declarations (Γ ++ Δ) := by
  induction left with
  | nil => exact right
  | cons head tail ih => exact .cons head ih

theorem TypesWF.lookup (formed : TypesWF declarations types)
    (found : lookup types index = some τ) : TyWF declarations τ := by
  induction formed generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => cases found; exact head
      | succ index => exact ih found

theorem ConstructorsWF.lookup (formed : ConstructorsWF declarations constructors)
    (found : lookup constructors index = some fields) : TypesWF declarations fields := by
  induction formed generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => cases found; exact head
      | succ index => exact ih found

theorem DeclarationTableWF.lookup (formed : DeclarationTableWF declarations table)
    (found : lookup table index = some constructors) : ConstructorsWF declarations constructors := by
  induction formed generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => cases found; exact head
      | succ index => exact ih found

theorem SignaturesWF.lookup (formed : SignaturesWF declarations signatures)
    (found : lookup signatures index = some signature) : SignatureWF declarations signature := by
  induction formed generalizing index with
  | nil => cases found
  | cons head tail ih =>
      cases index with
      | zero => cases found; exact head
      | succ index => exact ih found

theorem TyWF.prod_left (formed : TyWF declarations (.prod α β)) : TyWF declarations α := by
  cases formed with
  | prod left _ => exact left

theorem TyWF.prod_right (formed : TyWF declarations (.prod α β)) : TyWF declarations β := by
  cases formed with
  | prod _ right => exact right

theorem TyWF.sum_left (formed : TyWF declarations (.sum α β)) : TyWF declarations α := by
  cases formed with
  | sum left _ => exact left

theorem TyWF.sum_right (formed : TyWF declarations (.sum α β)) : TyWF declarations β := by
  cases formed with
  | sum _ right => exact right

theorem TyWF.array_item (formed : TyWF declarations (.array α)) : TyWF declarations α := by
  cases formed with
  | array item => exact item

end LeanExe.TypeSafety
