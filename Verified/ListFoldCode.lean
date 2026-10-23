import Verified.ListFoldState

namespace Verified

open Wasm

theorem argsMax_le {n : Nat} (f : Fin n → Nat) (bound : Nat) (h : ∀ i, f i ≤ bound) :
    argsMax f ≤ bound := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    change max (f 0) (argsMax fun i => f i.succ) ≤ bound
    exact Nat.max_le.mpr ⟨h 0, ih _ (fun i => h i.succ)⟩

theorem Ty.copyScratch_le_tree (t : Ty) : t.copyScratch ≤ treeCopyScratch := by
  induction t with
  | elem e => exact Nat.zero_le _
  | array e => change 3 ≤ 6; decide
  | bytes => change 2 ≤ 6; decide
  | tree shape => exact le_rfl
  | treeHeader shape => change 1 ≤ 6; decide
  | pair a b ha hb => exact Nat.max_le.mpr ⟨ha, hb⟩

namespace ListFold

theorem leafCode_self {S : List Sig} {Γ : List Ty} {t : Ty} (body : Expr S Γ t)
    (h : Nat) (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    leafCode h (fun slots base live => body.code h slots base live) body slots base live =
      body.code h slots base live := by
  cases body <;> rfl

theorem leafCode_var {S : List Sig} {Γ : List Ty} {t : Ty}
    (bodyCode : List Slot → Nat → (Nat → Bool) → Program)
    (h : Nat) (x : Var Γ t) (slots : List Slot) (base : Nat) (live : Nat → Bool) :
    leafCode (S := S) h bodyCode (.var x) slots base live = x.code h slots base live := rfl

theorem loopCode_eq {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (h stateBase : Nat) :
    loopCode body h stateBase (fun slots base live => body.code h slots base live) =
      let stateSlots := paramSlots (params e captures) [] stateBase
      let resultBase := stateBase + widthSum (params e captures)
      [.block 0 0 [.loop 0 0
        (releaseWhere (params e captures) stateSlots (fun i => !(tailBody body).usesFast i) ++
          (tailBody body).code [] h stateBase resultBase stateSlots (resultBase + e.width) 1 0)
        [] []] [] []] := by
  simp only [loopCode, TailBody.code, tailBody, TailBody.codeWith]
  simp only [nextArgs_get, leafCode_self, leafCode_var]
  rfl

theorem next_width {S : List Sig} {e : Elem} {captures : List Ty} :
    (TailBody.next (result := .elem e) (nextArgs (S := S) e captures).get).width [] ≤
      treeCopyScratch := by
  apply argsMax_le
  intro i
  simp only [paramMode_default, nextArgs_get, Expr.width]
  exact Ty.copyScratch_le_tree _

theorem tail_width {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) :
    (tailBody body).width [] ≤ 3 + max treeCopyScratch (e.width + max body.width treeCopyScratch) := by
  have hn := next_width (S := S) (e := e) (captures := captures)
  change max (max 0 0)
    (3 + max treeCopyScratch
      (e.width + max body.width
        ((TailBody.next (result := .elem e) (nextArgs (S := S) e captures).get).width []))) ≤ _
  rw [Nat.max_self, Nat.zero_max]
  exact Nat.add_le_add_left
    (max_le_max le_rfl (Nat.add_le_add_left (max_le_max le_rfl hn) _)) _

#print axioms loopCode_eq
#print axioms tail_width

end ListFold
end Verified
