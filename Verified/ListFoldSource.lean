import Verified.ContextAppend
import Verified.ListFoldDefs
import Verified.Rename

namespace Verified

theorem Args.vars_get_ofFin {S : List Sig} {Γ : List Ty} (ps : List Ty)
    (vars : Renaming ps Γ) (i : Fin ps.length) :
    (Args.vars (S := S) ps vars).get i = .var (vars (Var.ofFin ps i)) := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact ih (fun x => vars (.there x)) j

theorem Args.vars_get_image {S : List Sig} {Γ : List Ty} (ps : List Ty)
    (vars : Renaming ps Γ) (i : Fin ps.length) :
    ∃ x, (Args.vars (S := S) ps vars).get i = .var (vars x) := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨.here, rfl⟩
    · obtain ⟨x, hx⟩ := ih (fun x => vars (.there x)) j
      exact ⟨.there x, hx⟩

theorem Args.vars_get_var {S : List Sig} {Γ : List Ty} (ps : List Ty)
    (vars : Renaming ps Γ) (i : Fin ps.length) :
    ∃ x, (Args.vars (S := S) ps vars).get i = .var x := by
  obtain ⟨x, hx⟩ := Args.vars_get_image ps vars i
  exact ⟨vars x, hx⟩

theorem Args.vars_denote {S : List Sig} {Γ : List Ty} (ps : List Ty)
    (vars : Renaming ps Γ) (funs : Funs S) (env : Env Γ) :
    Env.ofFn (fun i => ((Args.vars (S := S) ps vars).get i).denote funs env) =
      env.remap vars := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change Env.cons (env.get (vars .here))
      (Env.ofFn (fun i => ((Args.vars ps (fun x => vars (.there x))).get i).denote funs env)) = _
    rw [ih]
    rfl

namespace ListFold

theorem nextArgs_get {S : List Sig} (e : Elem) (captures : List Ty)
    (i : Fin (params e captures).length) :
    (nextArgs (S := S) e captures).get i = .var (nextVar e captures i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · exact Args.vars_get_ofFin captures _ k

theorem next_uses {S : List Sig} {e : Elem} {captures : List Ty} (i : Nat) :
    (TailBody.next (result := .elem e) (nextArgs (S := S) e captures).get).uses (i + 1) =
      bodyLive e captures i := by
  simp only [TailBody.uses, bodyLive]
  congr 1
  funext j
  rw [nextArgs_get]
  rfl

theorem nextArgs_get_var {S : List Sig} (e : Elem) (captures : List Ty)
    (i : Fin (params e captures).length) :
    ∃ x, (nextArgs (S := S) e captures).get i = .var x := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨.there (.there (.there .here)), rfl⟩
  · refine Fin.cases ?_ (fun k => ?_) j
    · exact ⟨.here, rfl⟩
    · exact Args.vars_get_var captures _ k

theorem nextArgs_denote {S : List Sig} {e : Elem} {captures : List Ty}
    (funs : Funs S) (root tail : Tree listShape) (head : UInt64)
    (acc value : e.denote) (captured : Env captures) :
    Env.ofFn (fun i => ((nextArgs (S := S) e captures).get i).denote funs
      (.cons value (Env.treeFields listShape listCell (fun _ => head) (noFields rfl) (noFields rfl) (fun _ => tail)
        (.cons root (.cons acc captured))))) = .cons tail (.cons value captured) := by
  change Env.cons (t := .tree listShape) tail (Env.cons (t := .elem e) value
    (Env.ofFn (fun i => ((Args.vars captures (fun x => x.suffix
      [.elem e, .treeHeader listShape listCell, .word, .tree listShape, .tree listShape,
        .elem e])).get i).denote
        funs (.cons (t := .elem e) value (Env.treeFields listShape listCell (fun _ => head) (noFields rfl) (noFields rfl)
          (fun _ => tail)
          (.cons root (.cons acc captured))))))) = _
  rw [Args.vars_denote]
  congr 2
  apply Env.ext_get
  intro t x
  rw [Env.get_remap]
  rfl

theorem tailBody_denote {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (funs : Funs S)
    (root : Tree listShape) (acc : e.denote) (captured : Env captures) :
    (tailBody body).denote funs (.cons root (.cons acc captured)) =
      match root with
      | .nil _ => .inr acc
      | .node r words arrays buffers children => .inl (.cons (children ⟨0, listShape_children_pos r⟩)
          (.cons (body.denote funs (Env.treeFields listShape listCell (fun _ => words ⟨0, listShape_words_pos r⟩) (noFields rfl) (noFields rfl)
            (fun _ => children ⟨0, listShape_children_pos r⟩)
            (.cons root (.cons acc captured)))) captured)) := by
  cases root with
  | nil => rfl
  | node r words arrays buffers children =>
    obtain rfl := listShape_cell r
    simp only [tailBody, TailBody.denote, Env.get, listCell, listBranch]
    congr 1
    rw [listCell_words_eq words, listCell_children_eq children]
    exact nextArgs_denote funs _ _ _ _ _ _

theorem fixed {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (funs : Funs S)
    (state : Env (params e captures)) :
    meaning body funs state = ((tailBody body).denote funs state).elim (meaning body funs) id := by
  cases state with
  | cons root state =>
    cases state with
    | cons acc captured =>
      rw [tailBody_denote]
      cases root with
      | nil => rfl
      | node r words arrays buffers children =>
        simp only [meaning, denoteWith, Sum.elim_inl]
        congr 2

theorem decreases {S : List Sig} {e : Elem} {captures : List Ty}
    (body : Expr S (context e captures) (.elem e)) (funs : Funs S)
    (state next : Env (params e captures))
    (h : (tailBody body).denote funs state = .inl next) :
    (next.get .here).nodes < (state.get .here).nodes := by
  cases state with
  | cons root state =>
    cases state with
    | cons acc captured =>
      rw [tailBody_denote] at h
      cases root with
      | nil => contradiction
      | node r words arrays buffers children =>
        obtain rfl := listShape_cell r
        cases h
        change (children ⟨0, listShape_children_pos listCell⟩).nodes <
          1 + (List.ofFn fun i => (children i).nodes).sum
        rw [listCell_children_eq children]
        change _ < 1 + (List.ofFn (n := 1) fun _ => _).sum
        simp only [List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil]
        omega

end ListFold
end Verified
