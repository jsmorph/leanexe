/-!
Facts about lists of events and about an array after a list of writes, which the memory-model
proofs of the WGSL and PTX targets share.
-/

namespace LeanExe

theorem getElem?_append_some {l : List α} (new : List α) {k : Nat} {a : α} (h : l[k]? = some a) :
    (l ++ new)[k]? = some a := by
  obtain ⟨hk, -⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.getElem?_append_left hk, h]

theorem getElem?_append_singleton {l : List α} {a b : α} {k : Nat} (h : (l ++ [a])[k]? = some b) :
    l[k]? = some b ∨ (k = l.length ∧ a = b) := by
  rcases Nat.lt_or_ge k l.length with hk | hk
  · left
    rwa [List.getElem?_append_left hk] at h
  · right
    rw [List.getElem?_append_right hk] at h
    obtain ⟨j, rfl⟩ : ∃ j, k = l.length + j := ⟨k - l.length, by omega⟩
    cases j <;> simp at h ⊢
    exact h

/-- An array after the writes `ws` in order: write `w` stores `w.2` at index `w.1`, and a write
outside the array changes nothing. -/
def setAll (out : Array α) (ws : List (Nat × α)) : Array α :=
  ws.foldl (fun out w => out.setIfInBounds w.1 w.2) out

/-- The value at index `i` after the writes `ws`, starting from `v`. -/
def lastVal (ws : List (Nat × α)) (i : Nat) (v : α) : α :=
  ws.foldl (fun acc w => if w.1 = i then w.2 else acc) v

theorem lastVal_cons (w : Nat × α) (ws : List (Nat × α)) (i : Nat) (v : α) :
    lastVal (w :: ws) i v = lastVal ws i (if w.1 = i then w.2 else v) := rfl

theorem lastVal_append (a b : List (Nat × α)) (i : Nat) (v : α) :
    lastVal (a ++ b) i v = lastVal b i (lastVal a i v) := by
  simp [lastVal, List.foldl_append]

theorem lastVal_of_forall {ws : List (Nat × α)} {i : Nat} (h : ∀ w ∈ ws, w.1 ≠ i) (v : α) :
    lastVal ws i v = v := by
  induction ws generalizing v with
  | nil => rfl
  | cons w ws ih =>
      have hw : w.1 ≠ i := h w (by simp)
      rw [lastVal_cons, ih fun w' hw' => h w' (by simp [hw'])]
      simp [hw]

theorem setAll_append (out : Array α) (a b : List (Nat × α)) :
    setAll (setAll out a) b = setAll out (a ++ b) := by
  simp [setAll, List.foldl_append]

theorem setAll_get {out : Array α} {i : Nat} (hi : i < out.size) (ws : List (Nat × α)) :
    (setAll out ws)[i]? = some (lastVal ws i out[i]) := by
  induction ws generalizing out with
  | nil => simp [setAll, lastVal, getElem?_pos out i hi]
  | cons w ws ih =>
      have hs : i < (out.setIfInBounds w.1 w.2).size := by simpa using hi
      have hv : (out.setIfInBounds w.1 w.2)[i] = if w.1 = i then w.2 else out[i] :=
        Array.getElem_setIfInBounds hi
      show (setAll (out.setIfInBounds w.1 w.2) ws)[i]? = _
      rw [ih hs, hv]
      rfl

/-- After the writes of `W 0`, ..., `W (n - 1)`, when only `W g0` writes index `i`. -/
theorem lastVal_flatMap (W : Nat → List (Nat × α)) (i g0 N : Nat)
    (hu : ∀ g, g < N → g ≠ g0 → ∀ w ∈ W g, w.1 ≠ i) (v : α) :
    ∀ n, n ≤ N → lastVal ((List.range n).flatMap W) i v =
      if g0 < n then lastVal (W g0) i v else v := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
      intro hn
      rw [List.range_succ, List.flatMap_append, lastVal_append, ih (by omega)]
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      by_cases hg : n = g0
      · subst hg
        simp
      · rw [lastVal_of_forall (hu n (by omega) hg)]
        by_cases h0 : g0 < n
        · simp [h0, show g0 < n + 1 by omega]
        · simp [h0, show ¬g0 < n + 1 by omega]

end LeanExe
