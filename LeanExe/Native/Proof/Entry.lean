import LeanExe.Native.Proof.Dispatch

/-!
Function entry: the parameters bound by `function_entry2`, the declared locals set to 0 by the
statements that begin a translated function, and the inversion of `trFunction`.
-/

namespace LeanExe.Native

open Wasm LClight

theorem bind_params (ps : List VT) (start : Nat) (vs : List val) (le0 : temp_env)
    (hlen : vs.length = ps.length) :
    ∃ le1, bind_parameter_temps ((ps.zipIdx start).map fun x => (localId x.2, x.1.ty)) vs le0 =
        some le1 ∧
      (∀ i, i < ps.length → le1[localId (start + i)]? = vs[i]?) ∧
      (∀ x, (∀ i, i < ps.length → x ≠ localId (start + i)) → le1[x]? = le0[x]?) := by
  induction ps generalizing start vs le0 with
  | nil =>
      cases vs with
      | nil => exact ⟨le0, rfl, fun i hi => by simp at hi, fun _ _ => rfl⟩
      | cons _ _ => simp at hlen
  | cons p ps ih =>
      cases vs with
      | nil => simp at hlen
      | cons v vs =>
          simp at hlen
          obtain ⟨le1, h1, hget, hother⟩ := ih (start + 1) vs (le0.insert (localId start) v) hlen
          refine ⟨le1, by simpa [List.zipIdx_cons, bind_parameter_temps] using h1, ?_, ?_⟩
          · intro i hi
            cases i with
            | zero =>
                rw [hother _ (fun j _ e => by have := localId_inj e; omega)]
                simp
            | succ i =>
                have := hget i (by simp at hi; omega)
                rw [show start + (i + 1) = start + 1 + i by omega, this]
                simp
          · intro x hx
            rw [hother x (fun i hi => by
              have := hx (i + 1) (by simp; omega)
              rwa [show start + 1 + i = start + (i + 1) by omega])]
            exact te_insert_ne _ (fun e => hx 0 (by simp) (by simpa using e.symm))

/-- The environment after the statements that set the declared locals to 0. -/
def setLocals (le : temp_env) (np : Nat) : List (VT × Nat) → temp_env
  | [] => le
  | (t, j) :: rest => setLocals (le.insert (localId (np + j)) (zval t)) np rest

theorem setLocals_get (le : temp_env) (np : Nat) (ls : List VT) (start : Nat) :
    (∀ j, j < ls.length →
      ∃ t, ls[j]? = some t ∧ (setLocals le np (ls.zipIdx start))[localId (np + start + j)]? = some (zval t)) ∧
    (∀ x, (∀ j, j < ls.length → x ≠ localId (np + start + j)) →
      (setLocals le np (ls.zipIdx start))[x]? = le[x]?) := by
  induction ls generalizing le start with
  | nil => exact ⟨fun j hj => by simp at hj, fun _ _ => rfl⟩
  | cons t ls ih =>
      obtain ⟨hget, hother⟩ := ih (le.insert (localId (np + start)) (zval t)) (start + 1)
      simp only [List.zipIdx_cons, setLocals]
      refine ⟨fun j hj => ?_, fun x hx => ?_⟩
      · cases j with
        | zero =>
            refine ⟨t, rfl, ?_⟩
            rw [hother _ (fun j _ e => by have := localId_inj e; omega)]
            simp
        | succ j =>
            obtain ⟨t', ht', hl⟩ := hget j (by simp at hj; omega)
            exact ⟨t', by simpa using ht', by rw [show np + start + (j + 1) = np + (start + 1) + j by omega]; exact hl⟩
      · rw [hother x (fun j hj => by
          have := hx (j + 1) (by simp; omega)
          rwa [show np + (start + 1) + j = np + start + (j + 1) by omega])]
        exact te_insert_ne _ (fun e => hx 0 (by simp) (by simpa using e.symm))

theorem exec_setLocals {A : Archi} {X : ExtSem} {ge : genv} (np : Nat) (ls : List (VT × Nat))
    (rest : List statement) (hrest : rest ≠ []) {le : temp_env} {m : mem} {t : trace}
    {le' : temp_env} {m' : mem} {out : outcome}
    (h : exec_stmt A X ge empty_env (setLocals le np ls) m (seqList rest) t le' m' out) :
    ∃ t', exec_stmt A X ge empty_env le m
      (seqList ((ls.map fun x => statement.Sset (localId (np + x.2)) x.1.zero) ++ rest))
      t' le' m' out := by
  induction ls generalizing le with
  | nil => exact ⟨t, by simpa [setLocals] using h⟩
  | cons x ls ih =>
      obtain ⟨t', h'⟩ := ih h
      have hs : exec_stmt A X ge empty_env le m (.Sset (localId (np + x.2)) x.1.zero) E0
          (le.insert (localId (np + x.2)) (zval x.1)) m .Out_normal :=
        .exec_Sset _ _ _ _ _ _ (eval_zero A ge empty_env le m x.1)
      refine ⟨E0 ++ t', ?_⟩
      have hne : (ls.map fun x => statement.Sset (localId (np + x.2)) x.1.zero) ++ rest ≠ [] := by
        simp [hrest]
      obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.map_cons, List.cons_append, seqList]
      rw [hl] at h' ⊢
      exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hs (by simpa [setLocals] using h')

/-- The inversion of `trFunction`. -/
theorem trFunction_spec {cap : Nat} {sigs : List (Option (List VT × List VT))} {G : Nat}
    {f : Function} {fd : function} {al : Bool} (h : trFunction cap sigs G f al = some fd) :
    ∃ ps ls rs body nc, f.params.mapM VT.ofValueType = some ps ∧
      f.locals.mapM VT.ofValueType = some ls ∧ f.results.mapM VT.ofValueType = some rs ∧
      resultsOk rs = true ∧
      trProg { locals := ps ++ ls, results := rs, nglobals := G, sigs := sigs, cap := cap,
               alignedAccess := al }
        [{ isLoop := false, base := 0, result := retOf rs, final := 2 ≤ rs.length }] []
        rs.reverse 0 f.body = some (body, nc) ∧
      fd = { fn_return := ((retOf rs).map VT.ty).getD .Tvoid, fn_callconv := cc_default,
             fn_params := (ps.zipIdx).map fun x => (localId x.2, x.1.ty), fn_vars := [],
             fn_temps := (ls.zipIdx).map (fun x => (localId (ps.length + x.2), x.1.ty)) ++
               bodyTemps body,
             fn_body := seqList ((ls.zipIdx).map (fun x => statement.Sset (localId (ps.length + x.2))
               x.1.zero) ++ [.Sset brkId (cint 0), limSet, wrapLoop body, retStmt rs]) } := by
  simp [trFunction, Option.bind_eq_some_iff] at h
  obtain ⟨ps, hps, ls, hls, rs, hrs, hok, body, ⟨nc, hb⟩, rfl⟩ := h
  exact ⟨ps, ls, rs, body, nc, hps, hls, hrs, hok, hb, rfl⟩

end LeanExe.Native
