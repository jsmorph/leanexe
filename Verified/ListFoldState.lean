import Verified.ListFoldSource
import Verified.TailBound
import Verified.FieldsOrder

namespace Verified

@[simp] theorem Ty.paramMode_borrowed (t : Ty) : t.paramMode .borrowed = .borrowed := by
  cases t <;> rfl

@[simp] theorem paramModes_default (ps : List Ty) :
    paramModes ps [] = List.replicate ps.length .borrowed := by
  induction ps with
  | nil => rfl
  | cons t ps ih =>
    change t.paramMode .borrowed :: paramModes ps [] = List.replicate (ps.length + 1) .borrowed
    rw [Ty.paramMode_borrowed, ih, List.replicate_succ]

@[simp] theorem paramMode_default (ps : List Ty) (i : Nat) :
    paramMode ps [] i = .borrowed := by
  simp only [paramMode, paramModes_default, List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> rfl

namespace ListFold

theorem nextArgs_borrowed {S : List Sig} {e : Elem} {captures : List Ty}
    (mode : Mode) (modes : List Mode) (borrowed : ∀ i, modes.getD i .borrowed = .borrowed)
    (i : Fin (params e captures).length) :
    ((params e captures).get i).scalar = false →
      ((nextArgs (S := S) e captures).get i).mode (mode :: modes) = .borrowed := by
  refine Fin.cases ?_ (fun j => ?_) i
  · intro _
    change modes.getD 2 .borrowed = .borrowed
    exact borrowed 2
  · refine Fin.cases ?_ (fun k => ?_) j
    · intro h
      exact Bool.noConfusion h
    · intro _
      let vars : Renaming captures
          ([.elem e, .treeHeader listShape, .word, .tree listShape, .tree listShape, .elem e] ++
            captures) := fun x => x.suffix _
      obtain ⟨x, hx⟩ := Args.vars_get_image (S := S) captures vars k
      change ((Args.vars (S := S) captures vars).get k).mode (mode :: modes) = .borrowed
      rw [hx]
      change (mode :: modes).getD (x.suffix _).index .borrowed = .borrowed
      rw [Var.suffix_index]
      change (mode :: modes).getD (6 + x.index) .borrowed = .borrowed
      rw [Nat.add_comm 6 x.index]
      change modes.getD (x.index + 5) .borrowed = .borrowed
      exact borrowed _

theorem next_placeArgs {S : List Sig} {e : Elem} {captures : List Ty}
    (mode : Mode) (modes : List Mode) (borrowed : ∀ i, modes.getD i .borrowed = .borrowed) :
    (TailBody.next (result := .elem e) (nextArgs (S := S) e captures).get).placeArgs []
      (mode :: modes) = true := by
  simp only [TailBody.placeArgs, Bool.and_eq_true, Bool.not_eq_true']
  constructor
  · have he : (fun i => !((nextArgs (S := S) e captures).get i).placeArgs) = fun _ => false := by
      funext i
      obtain ⟨x, hx⟩ := nextArgs_get_var (S := S) e captures i
      simp [hx, Expr.placeArgs]
    rw [he]
    exact argsAny_false _
  · have he : (fun i : Fin (params e captures).length =>
        !((params e captures).get i).scalar &&
        if paramMode (params e captures) [] i == .owned then
          ((nextArgs (S := S) e captures).get i).varIndex?.isNone
        else !((nextArgs (S := S) e captures).get i).isPlace ||
          ((nextArgs (S := S) e captures).get i).mode (mode :: modes) != .borrowed) =
        fun _ => false := by
      funext i
      obtain ⟨x, hx⟩ := nextArgs_get_var (S := S) e captures i
      cases hs : ((params e captures).get i).scalar
      · have hb := nextArgs_borrowed (S := S) (e := e) (captures := captures) mode modes borrowed i hs
        rw [hx] at hb
        simp [hx, Expr.isPlace, hb]
      · simp
    rw [he]
    exact argsAny_false _

theorem tailBody_placeArgs {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (h : body.placeArgs = true) :
    (tailBody body).placeArgs [] (paramModes (params e captures) []) = true := by
  let modes := paramModes (params e captures) []
  have borrowed (i : Nat) : modes.getD i .borrowed = .borrowed := paramMode_default _ i
  have root : modes.getD (Var.here : Var (params e captures) (.tree listShape)).index
      .borrowed = .borrowed := borrowed 0
  have fields (i : Nat) : (listShape.modes .borrowed modes).getD i .borrowed = .borrowed := by
    change (.borrowed :: .borrowed :: .borrowed :: modes).getD i .borrowed = .borrowed
    cases i with
    | zero => rfl
    | succ i => cases i with
      | zero => rfl
      | succ i => cases i with
        | zero => rfl
        | succ i => exact borrowed i
  change (tailBody body).placeArgs [] modes = true
  simp only [tailBody, TailBody.placeArgs, Expr.placeArgs, Bool.true_and, h, root]
  exact next_placeArgs (S := S) (e := e) (captures := captures)
    (body.mode (listShape.modes .borrowed modes)) _ fields

def func {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true) : TailFunc S :=
  { name := "listFold"
    params := params e captures
    result := .elem e
    modes := []
    body := tailBody body
    placeArgs := tailBody_placeArgs body place
    rank := fun _ state => (state.get .here).nodes }

theorem func_decreases {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (place : body.placeArgs = true)
    (funs : Funs S) : (func body place).Decreases funs :=
  decreases body funs

end ListFold
end Verified
