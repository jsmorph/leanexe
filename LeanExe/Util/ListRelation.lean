import Init.Data.List.Lemmas

namespace LeanExe

/-- An elementwise relation that also requires equal list lengths. -/
inductive ListRelation (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListRelation relation [] []
  | cons : relation x y → ListRelation relation xs ys → ListRelation relation (x :: xs) (y :: ys)

namespace ListRelation

theorem length {relation : α → β → Prop} {xs : List α} {ys : List β}
    (matched : ListRelation relation xs ys) : xs.length = ys.length := by
  induction matched with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem append {relation : α → β → Prop} {xs as : List α} {ys bs : List β}
    (first : ListRelation relation xs ys) (second : ListRelation relation as bs) :
    ListRelation relation (xs ++ as) (ys ++ bs) := by
  induction first with
  | nil => exact second
  | cons head _ ih => exact .cons head ih

theorem reverse {relation : α → β → Prop} {xs : List α} {ys : List β}
    (matched : ListRelation relation xs ys) : ListRelation relation xs.reverse ys.reverse := by
  induction matched with
  | nil => exact .nil
  | cons head _ ih => simpa using ih.append (.cons head .nil)

end ListRelation
end LeanExe
