import Verified.Source

namespace Verified

def listConsExpr : Expr S [.word, .tree listShape] (.tree listShape) :=
  .treeNode listCell none (fun _ => .v 0) (noFields rfl) (noFields rfl) (fun _ => .v 1)

def listFirstExpr : Expr S [.tree listShape] .word :=
  .treeCase .here (fun _ => .word 0) (listBranch (.v 1))

def listRestExpr : Expr S [.tree listShape] (.tree listShape) :=
  .treeCase .here (fun _ => .treeNil listShape rfl) (listBranch (.v 2))

def listRebuildExpr : Expr S [.tree listShape] (.tree listShape) :=
  .treeCase .here (fun _ => .treeNil listShape rfl)
    (listBranch (.treeNode listCell (some .here) (fun _ => .v 1) (noFields rfl) (noFields rfl)
      (fun _ => .v 2)))

theorem listConsExpr_denote (x : UInt64) (xs : List UInt64) :
    listConsExpr.denote .nil (.cons x (.cons (.ofList xs) .nil)) = .ofList (x :: xs) := rfl

theorem listFirstExpr_denote (xs : List UInt64) :
    listFirstExpr.denote .nil (.cons (.ofList xs) .nil) = xs.headD 0 := by
  cases xs <;> rfl

theorem listRestExpr_denote (xs : List UInt64) :
    listRestExpr.denote .nil (.cons (.ofList xs) .nil) = .ofList xs.tail := by
  cases xs <;> rfl

theorem listRebuildExpr_denote (xs : List UInt64) :
    listRebuildExpr.denote .nil (.cons (.ofList xs) .nil) = .ofList xs := by
  cases xs <;> rfl

example : (listRebuildExpr (S := [])).uses 0 = true := rfl

example : (listRebuildExpr (S := [])).mode [.owned] = .owned := rfl

example : (listRestExpr (S := [])).mode [.borrowed] = .owned := rfl

#print axioms listConsExpr_denote
#print axioms listFirstExpr_denote
#print axioms listRestExpr_denote
#print axioms listRebuildExpr_denote

end Verified
