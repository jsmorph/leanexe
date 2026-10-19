import Verified.TailPaid
import Verified.Reflect.TailModes

namespace Verified.Examples.TailModel

def growParams : List Ty := [.word, .array .word, .array .word]

def growBody : TailBody [] growParams (.array .word) growParams :=
  .ite (.cmp .eq (.v 0) (.word 0)) (.ret (.v 1))
    (.letE (.get (Var.ofIndex _ 2 rfl) (.bin .sub (.v 0) (.word 1)))
      (.letE (.push (Var.ofIndex _ 2 rfl) (.v 0))
        (.next (Args.cons (.bin .sub (.v 2) (.word 1))
          (.cons (.v 0) (.cons (.v 4) .nil))).get)))

theorem grow_modes : growBody.inferModes = [.borrowed, .owned, .borrowed] := rfl

theorem grow_places : growBody.placeArgs growBody.inferModes
    (paramModes growParams growBody.inferModes) = true := rfl

def grow : TailFunc [] where
  name := "grow"
  params := growParams
  result := .array .word
  modes := growBody.inferModes
  body := growBody
  placeArgs := grow_places
  rank := fun _ env => (env.get (Var.ofIndex _ 0 rfl)).toNat

theorem grow_step (n : UInt64) (xs weights : Array UInt64) :
    growBody.denote .nil (.cons n (.cons xs (.cons weights .nil))) =
      if n == 0 then .inr xs else
        .inl (.cons (n - 1) (.cons (xs.push weights[(n - 1).toNat]!) (.cons weights .nil))) := rfl

theorem grow_decreases : grow.Decreases .nil := by
  intro state next hs
  cases state with
  | cons n rest =>
    cases rest with
    | cons xs rest =>
      cases rest with
      | cons weights rest =>
        cases rest
        change growBody.denote .nil (.cons n (.cons xs (.cons weights .nil))) = _ at hs
        rw [grow_step] at hs
        by_cases hn : n = 0
        · simp [hn] at hs
        · simp only [beq_iff_eq, hn, ↓reduceIte] at hs
          cases Sum.inl.inj hs
          change (n - 1).toNat < n.toNat
          simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at hn ⊢
          omega

theorem grow_paid : grow.paidResult .nil = true := rfl

def rotateParams : List Ty := [.array .word, .array .word, .word]

def rotateBody : TailBody [] rotateParams (.array .word) rotateParams :=
  .ite (.cmp .eq (.v 2) (.word 0)) (.ret (.v 0))
    (.next (Args.cons (.v 1) (.cons (.v 0) (.cons (.bin .sub (.v 2) (.word 1)) .nil))).get)

theorem rotate_modes : rotateBody.inferModes = [.owned, .owned, .borrowed] := rfl

theorem rotate_places : rotateBody.placeArgs rotateBody.inferModes
    (paramModes rotateParams rotateBody.inferModes) = true := rfl

def replaceParams : List Ty := [.array .word, .word]

def replaceBody : TailBody [] replaceParams .word replaceParams :=
  .ite (.cmp .eq (.v 1) (.word 0)) (.ret (.size (Var.ofIndex _ 0 rfl)))
    (.letE (.build (.word 0) (.word 0))
      (.next (Args.cons (.v 0) (.cons (.bin .sub (.v 2) (.word 1)) .nil)).get))

theorem replace_modes : replaceBody.inferModes = [.owned, .borrowed] := rfl

theorem replace_places : replaceBody.placeArgs replaceBody.inferModes
    (paramModes replaceParams replaceBody.inferModes) = true := rfl

#print axioms grow_modes
#print axioms grow_places
#print axioms grow_decreases
#print axioms grow_paid
#print axioms rotate_modes
#print axioms replace_modes

end Verified.Examples.TailModel
