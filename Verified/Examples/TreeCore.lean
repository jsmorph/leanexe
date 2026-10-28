import Verified.TreeSource
import Verified.Compile
import Verified.Correct

namespace Verified.Examples.TreeCore

def cons (mode : Mode) : Func S :=
  { name := if mode = .owned then "consOwned" else "cons"
    params := [.word, .tree listShape], result := .tree listShape
    modes := [.borrowed, mode], body := listConsExpr, placeArgs := rfl }

def first (mode : Mode) : Func S :=
  { name := if mode = .owned then "firstOwned" else "first"
    params := [.tree listShape], result := .word
    modes := [mode], body := listFirstExpr, placeArgs := rfl }

def rest (mode : Mode) : Func S :=
  { name := if mode = .owned then "restOwned" else "rest"
    params := [.tree listShape], result := .tree listShape
    modes := [mode], body := listRestExpr, placeArgs := rfl }

def rebuild (mode : Mode) : Func S :=
  { name := if mode = .owned then "rebuildOwned" else "rebuild"
    params := [.tree listShape], result := .tree listShape
    modes := [mode], body := listRebuildExpr, placeArgs := rfl }

def duplicateExpr : Expr S [.tree listShape] (.pair (.tree listShape) (.tree listShape)) :=
  .treeCase .here (fun _ => .pair (.treeNil listShape rfl) (.v 0))
    (listBranch (.pair
      (.treeNode listCell (some .here) (fun _ => .v 1) (noFields rfl) (noFields rfl)
      (fun _ => .v 2)) (.v 3)))

def duplicate (mode : Mode) : Func S :=
  { name := if mode = .owned then "duplicateOwned" else "duplicate"
    params := [.tree listShape], result := .pair (.tree listShape) (.tree listShape)
    modes := [mode], body := duplicateExpr, placeArgs := rfl }

def changeExpr : Expr S [.word, .tree listShape] (.tree listShape) :=
  .treeCase (.there .here) (fun _ => .treeNil listShape rfl)
    (listBranch
      (.treeNode listCell (some .here) (fun _ => .bin .add (.v 1) (.v 3)) (noFields rfl)
        (noFields rfl) (fun _ => .v 2)))

def change (mode : Mode) : Func S :=
  { name := if mode = .owned then "changeOwned" else "change"
    params := [.word, .tree listShape], result := .tree listShape
    modes := [.borrowed, mode], body := changeExpr, placeArgs := rfl }

def foldWord (mode : Mode) : Func S :=
  { name := if mode = .owned then "foldWordOwned" else "foldWord"
    params := [.tree listShape, .word], result := .word
    modes := [mode, .borrowed]
    body := .listFold (e := .word) (captures := [])
      (Args.cons (.v 0) (.cons (.v 1) .nil)).get
      (.bin .add (.bin .mul (.v 4) (.word 3)) (.v 1))
    placeArgs := rfl }

def foldLookup (mode : Mode) : Func S :=
  { name := if mode = .owned then "foldLookupOwned" else "foldLookup"
    params := [.tree listShape, .word, .array .word], result := .word
    modes := [mode, .borrowed, mode]
    body := .listFold (e := .word) (captures := [.array .word])
      (Args.cons (.v 0) (.cons (.v 1) (.cons (.v 2) .nil))).get
      (.bin .add (.v 4) (.get (Var.ofIndex _ 5 rfl) (.v 1)))
    placeArgs := rfl }

def foldBuild (mode : Mode) : Func S :=
  { name := if mode = .owned then "foldBuildOwned" else "foldBuild"
    params := [.tree listShape, .word], result := .word
    modes := [mode, .borrowed]
    body := .listFold (e := .word) (captures := [])
      (Args.cons (.v 0) (.cons (.v 1) .nil)).get
      (.letE (.build (.word 2) (.bin .add (.v 0) (.v 2)))
        (.bin .add (.v 5) (.get .here (.word 1))))
    placeArgs := rfl }

def prog :=
  Prog.cons (foldBuild .owned) <| .cons (foldBuild .borrowed) <|
  .cons (foldLookup .owned) <| .cons (foldLookup .borrowed) <|
  .cons (foldWord .owned) <| .cons (foldWord .borrowed) <|
  .cons (change .owned) <| .cons (change .borrowed) <|
  .cons (duplicate .owned) <| .cons (duplicate .borrowed) <|
  .cons (rebuild .owned) <| .cons (rebuild .borrowed) <|
  .cons (rest .owned) <| .cons (rest .borrowed) <|
  .cons (first .owned) <| .cons (first .borrowed) <|
  .cons (cons .owned) <| .cons (cons .borrowed) .nil

def module : Wasm.Module := compile prog

theorem correct : Calls module prog.funs prog.flags
    (prog.boundsAt prog.funs) (prog.fitsAt prog.funs) Bytes.LiteralPool.empty :=
  prog.correct_funs rfl (by decide +kernel)

theorem duplicate_denote (xs : List UInt64) :
    duplicateExpr.denote .nil (.cons (.ofList xs) .nil) = (.ofList xs, .ofList xs) := by
  cases xs <;> rfl

theorem change_denote (x : UInt64) (xs : List UInt64) :
    changeExpr.denote .nil (.cons x (.cons (.ofList xs) .nil)) =
      .ofList (match xs with | [] => [] | y :: ys => (y + x) :: ys) := by
  cases xs <;> rfl

#print axioms duplicate_denote
#print axioms change_denote
#print axioms correct

end Verified.Examples.TreeCore
