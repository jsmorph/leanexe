import LeanExe.TypeSafety.Typing

/-!
# Independent scalar64 admission

This profile is a restriction of the independently specified TypeSafety language.
Its grammar and typing judgments do not mention the extractor or WASM emitter.
Word literals are checked by ordinary typing, including their 64-bit bound.
Unused bindings are allowed and retain the core's strict evaluation semantics.
Call graph and loop-lowering obligations are separate from this expression grammar.
-/

namespace LeanExe.Correct.Scalar64

open LeanExe.TypeSafety

mutual
  inductive Shape : Expr → Prop where
    | var : Shape (.var index)
    | bool : Shape (.bool value)
    | word : Shape (.word .w64 value)
    | letE : Shape value → Shape body → Shape (.letE value body)
    | ifE : Shape condition → Shape yes → Shape no → Shape (.ifE condition yes no)
    | bin : Shape left → Shape right → Shape (.wordBin .w64 op left right)
    | cmp : Shape left → Shape right → Shape (.wordCmp .w64 op left right)
    | call : Shapes args → Shape (.call index args)

  inductive Shapes : List Expr → Prop where
    | nil : Shapes []
    | cons : Shape head → Shapes tail → Shapes (head :: tail)
end

mutual
  def checkShape : Expr → Bool
    | .var _ | .bool _ | .word .w64 _ => true
    | .letE value body => checkShape value && checkShape body
    | .ifE condition yes no => checkShape condition && checkShape yes && checkShape no
    | .wordBin .w64 _ left right | .wordCmp .w64 _ left right =>
        checkShape left && checkShape right
    | .call _ args => checkShapes args
    | _ => false

  def checkShapes : List Expr → Bool
    | [] => true
    | head :: tail => checkShape head && checkShapes tail
end

mutual
  theorem checkShape_complete (h : Shape e) : checkShape e = true := by
    cases h with
    | var | bool | word => rfl
    | letE hv hb => simp [checkShape, checkShape_complete hv, checkShape_complete hb]
    | ifE hc hy hn =>
        simp [checkShape, checkShape_complete hc, checkShape_complete hy, checkShape_complete hn]
    | bin hl hr | cmp hl hr =>
        simp [checkShape, checkShape_complete hl, checkShape_complete hr]
    | call ha => exact checkShapes_complete ha

  theorem checkShapes_complete (h : Shapes es) : checkShapes es = true := by
    cases h with
    | nil => rfl
    | cons hh ht => simp [checkShapes, checkShape_complete hh, checkShapes_complete ht]
end

mutual
  theorem checkShape_sound (e : Expr) (h : checkShape e = true) : Shape e := by
    cases e with
    | var => exact .var
    | bool => exact .bool
    | word width => cases width with
        | w8 => cases h
        | w32 => cases h
        | w64 => exact .word
    | letE value body =>
        exact .letE (checkShape_sound value (Bool.and_eq_true_iff.mp h).1)
          (checkShape_sound body (Bool.and_eq_true_iff.mp h).2)
    | ifE condition yes no =>
        obtain ⟨hcy, hn⟩ := Bool.and_eq_true_iff.mp h
        obtain ⟨hc, hy⟩ := Bool.and_eq_true_iff.mp hcy
        exact .ifE (checkShape_sound condition hc) (checkShape_sound yes hy)
          (checkShape_sound no hn)
    | wordBin width op left right =>
        cases width with
        | w8 => cases h
        | w32 => cases h
        | w64 =>
            exact .bin (checkShape_sound left (Bool.and_eq_true_iff.mp h).1)
              (checkShape_sound right (Bool.and_eq_true_iff.mp h).2)
    | wordCmp width op left right =>
        cases width with
        | w8 => cases h
        | w32 => cases h
        | w64 =>
            exact .cmp (checkShape_sound left (Bool.and_eq_true_iff.mp h).1)
              (checkShape_sound right (Bool.and_eq_true_iff.mp h).2)
    | call index args => exact .call (checkShapes_sound args h)
    | _ => simp [checkShape] at h

  theorem checkShapes_sound (es : List Expr) (h : checkShapes es = true) : Shapes es := by
    cases es with
    | nil => exact .nil
    | cons head tail =>
        exact .cons (checkShape_sound head (Bool.and_eq_true_iff.mp h).1)
          (checkShapes_sound tail (Bool.and_eq_true_iff.mp h).2)
end

theorem checkShape_iff : checkShape e = true ↔ Shape e :=
  ⟨checkShape_sound e, checkShape_complete⟩

theorem checkShapes_iff : checkShapes es = true ↔ Shapes es :=
  ⟨checkShapes_sound es, checkShapes_complete⟩

def SignatureAllowed (sig : Signature) : Prop :=
  sig.result = .word .w64 ∧ ∀ ty ∈ sig.params, ty = .word .w64

def checkSignature (sig : Signature) : Bool :=
  decide (sig.result = .word .w64) && sig.params.all (fun ty => decide (ty = .word .w64))

/-- Pointwise list checking without function extensionality. -/
theorem all_true_iff (predicate : α → Bool) (values : List α) :
    values.all predicate = true ↔ ∀ value ∈ values, predicate value = true := by
  induction values with
  | nil =>
      constructor
      · intro _ value impossible; cases impossible
      · intro _; rfl
  | cons head tail ih =>
      constructor
      · intro checked value member
        obtain ⟨hh, ht⟩ := Bool.and_eq_true_iff.mp checked
        rcases List.mem_cons.mp member with same | member
        · subst value; exact hh
        · exact ih.mp ht value member
      · intro checked
        exact Bool.and_eq_true_iff.mpr
          ⟨checked head (List.mem_cons_self),
            ih.mpr (fun value member => checked value (List.mem_cons_of_mem head member))⟩

theorem checkSignature_iff : checkSignature sig = true ↔ SignatureAllowed sig := by
  constructor
  · intro checked
    obtain ⟨result, params⟩ := Bool.and_eq_true_iff.mp checked
    exact ⟨of_decide_eq_true result,
      fun ty member => of_decide_eq_true ((all_true_iff _ _).mp params ty member)⟩
  · intro allowed
    exact Bool.and_eq_true_iff.mpr ⟨decide_eq_true allowed.1,
      (all_true_iff _ _).mpr (fun ty member => decide_eq_true (allowed.2 ty member))⟩

/-- Scalar syntax with independently checked ordinary typing. -/
def ProgramAllowed (program : Program) (signatures : Signatures) : Prop :=
  ProgramTyped [] program signatures ∧ Shapes program ∧
    ∀ sig ∈ signatures, SignatureAllowed sig

def checkProgram (program : Program) (signatures : Signatures) : Bool :=
  programWellTyped [] program signatures && checkShapes program &&
    signatures.all checkSignature

theorem checkProgram_iff : checkProgram program signatures = true ↔
    ProgramAllowed program signatures := by
  constructor
  · intro checked
    obtain ⟨first, signaturesChecked⟩ := Bool.and_eq_true_iff.mp checked
    obtain ⟨typed, shaped⟩ := Bool.and_eq_true_iff.mp first
    exact ⟨programWellTyped_iff.mp typed, checkShapes_iff.mp shaped,
      fun sig member => checkSignature_iff.mp
        ((all_true_iff _ _).mp signaturesChecked sig member)⟩
  · rintro ⟨typed, shaped, signaturesAllowed⟩
    exact Bool.and_eq_true_iff.mpr
      ⟨Bool.and_eq_true_iff.mpr
        ⟨programWellTyped_iff.mpr typed, checkShapes_iff.mpr shaped⟩,
        (all_true_iff _ _).mpr (fun sig member =>
          checkSignature_iff.mpr (signaturesAllowed sig member))⟩

theorem admitted_type_safety
    (admitted : checkProgram program signatures = true)
    (typed : ExprTyped [] signatures [] expr ty)
    (execution : Steps program (initial expr) final) :
    StateTyped [] signatures final ty ∧ ¬ Stuck program final :=
  closed_type_safety (checkProgram_iff.mp admitted).1 typed execution

end LeanExe.Correct.Scalar64
