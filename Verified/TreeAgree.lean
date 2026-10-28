import Verified.Correct

namespace Verified

open Wasm LeanExe.Pipeline LeanExe.Runtime

theorem Agree.encode {α β : Type} [Encode α] [Encode β] [EncodeWellFormed α]
    [EncodeWellFormed β] (φ : α → β)
    (h : ∀ x, Encode.encode x = Encode.encode (φ x)) :
    Agree (inferInstanceAs (Represent α)) (inferInstanceAs (Represent β)) φ where
  borrowed heap store vs x := by
    change (∃ p, vs = [.i64 p] ∧ NodeBorrowed heap store p (Encode.encode x)) ↔ _
    simp only [h]
  owned heap store vs x := by
    change (∃ p, vs = [.i64 p] ∧ NodeOwned heap store p (Encode.encode x) ∧
      (Node.blocks store p (Encode.encode x)).Pairwise regionsDisjoint) ↔ _
    simp only [h]
  width _ := rfl
  blocks store vs x := by cases vs with
    | nil => rfl
    | cons v vs => cases v <;> cases vs <;> simp only [Represent.blocks, h]
  reads store vs x := by cases vs with
    | nil => rfl
    | cons v vs => cases v <;> cases vs <;> simp only [Represent.reads, h]
  moves _ _ _ := rfl

theorem Agree.movedEncode {α β : Type} [Encode α] [Encode β] [EncodeWellFormed α]
    [EncodeWellFormed β] (φ : α → β)
    (h : ∀ x, Encode.encode x = Encode.encode (φ x)) :
    Agree (inferInstanceAs (Represent (Moved α)))
      (inferInstanceAs (Represent (Moved β))) (fun x : Moved α => (⟨φ x.val⟩ : Moved β)) where
  borrowed heap store vs x := (Agree.encode φ h).owned heap store vs x.val
  owned heap store vs x := (Agree.encode φ h).owned heap store vs x.val
  width _ := rfl
  blocks store vs x := (Agree.encode φ h).blocks store vs x.val
  reads _ _ _ := rfl
  moves store vs x := by cases vs with
    | nil => rfl
    | cons v vs => cases v <;> cases vs <;> simp only [Represent.moves, h]

theorem Agree.listTree : Agree (inferInstanceAs (Represent (List UInt64)))
    (Ty.tree listShape).leanInst Tree.ofList :=
  Agree.encode Tree.ofList (fun xs => (Tree.toNode_ofList xs).symm)

theorem Agree.movedListTree : Agree (inferInstanceAs (Represent (Moved (List UInt64))))
    ((Ty.tree listShape).argInst .owned)
      (fun xs : Moved (List UInt64) => (⟨Tree.ofList xs.val⟩ : Moved (Tree listShape))) :=
  Agree.movedEncode Tree.ofList (fun xs => (Tree.toNode_ofList xs).symm)

#print axioms Agree.encode
#print axioms Agree.movedEncode
#print axioms Agree.listTree
#print axioms Agree.movedListTree

end Verified
