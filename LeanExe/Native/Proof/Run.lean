import LeanExe.Native.Proof.Entry

/-!
The simulation of a call of a translated function: Talos's `run` against CompCert's
`eval_funcall`, from the function's entry through its body to its return.
-/

namespace LeanExe.Native

open Wasm LClight

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' → l'.length = l.length
  | [], l', h => by simp at h; subst h; rfl
  | a :: l, l', h => by
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨b, -, l'', hl, rfl⟩ := h
      simp [mapM_length hl]

theorem mapM_get {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {l' : List β}, l.mapM f = some l' →
      ∀ j (hj : j < l.length), ∃ b, f l[j] = some b ∧ l'[j]? = some b
  | [], _, _, j, hj => by simp at hj
  | a :: l, l', h, j, hj => by
      simp [Option.bind_eq_some_iff] at h
      obtain ⟨b, hb, l'', hl, rfl⟩ := h
      cases j with
      | zero => exact ⟨b, hb, rfl⟩
      | succ j =>
          obtain ⟨b', hb', hl'⟩ := mapM_get hl j (by simp at hj; omega)
          exact ⟨b', hb', by simpa using hl'⟩

theorem AllHas.get {ps : List VT} {vs : List Value} (h : AllHas ps vs) :
    ∀ i (hi : i < ps.length), ∃ v, vs[i]? = some v ∧ ps[i].has v = true := by
  induction ps generalizing vs with
  | nil => intro i hi; simp at hi
  | cons p ps ih =>
      cases vs with
      | nil => simp [AllHas] at h
      | cons v vs =>
          intro i hi
          cases i with
          | zero => exact ⟨v, rfl, h.1⟩
          | succ i =>
              obtain ⟨w, hw, ht⟩ := ih h.2 i (by simp at hi; omega)
              exact ⟨w, by simpa using hw, by simpa using ht⟩

theorem AllHas.length {ps : List VT} {vs : List Value} (h : AllHas ps vs) :
    vs.length = ps.length := by
  induction ps generalizing vs with
  | nil => cases vs <;> simp_all [AllHas]
  | cons p ps ih =>
      cases vs with
      | nil => simp [AllHas] at h
      | cons v vs => simp [ih h.2]

theorem callees_seqList (l : List statement) : callees (seqList l) = l.flatMap callees := by
  induction l with
  | nil => rfl
  | cons s rest ih =>
      cases rest with
      | nil => simp [seqList]
      | cons s' rest' => simp only [seqList] at ih ⊢; simp [callees, ih]

theorem mem_bodyTemps {body : statement} {x : ident × type} (h : x ∈ bodyTemps body) :
    x.1 % 8 ≠ 0 := by
  obtain ⟨id, ty⟩ := x
  show ¬ ((id : Nat) % 8 = 0)
  simp only [bodyTemps, List.mem_append, List.mem_filter, List.mem_reverse, List.mem_singleton]
    at h
  rcases h with (⟨-, h⟩ | h) | ⟨-, h⟩
  · simp only [decide_eq_true_eq] at h
    have key : ∀ n : Nat, 1 ≤ n % 8 ∧ n % 8 ≤ 4 → ¬ (n % 8 = 0) := by omega
    exact key id h
  · simp only [Prod.mk.injEq] at h
    rw [h.1]; decide
  · simp only [decide_eq_true_eq] at h
    have key : ∀ n : Nat, n % 8 = 6 → ¬ (n % 8 = 0) := by omega
    exact key id h

theorem var_names_params (ps : List VT) :
    var_names ((ps.zipIdx).map fun x => (localId x.2, x.1.ty)) =
      (List.range' 0 ps.length).map localId := by
  simp only [var_names, List.map_map]
  rw [show ((Prod.fst ∘ fun x : VT × Nat => (localId x.2, x.1.ty)) : VT × Nat → ident) =
    localId ∘ Prod.snd from rfl, ← List.map_map, List.zipIdx_map_snd]

theorem blocks_of_empty : blocks_of_env empty_env = [] := rfl

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module}

theorem outcome_value {t : VT} {v : Value} (ht : t.has v = true) (m : mem) :
    outcome_result_value (.Out_return (some (cval v, t.ty))) t.ty (cval v) m :=
  ⟨by cases t <;> simp [VT.ty], cast_cval ht m⟩

theorem outcome_zero (t : VT) (m : mem) :
    outcome_result_value (.Out_return (some (zval t, t.ty))) t.ty (zval t) m :=
  ⟨by cases t <;> simp [VT.ty], cast_zval t m⟩

/-- The simulation of a call of a translated function whose callees are simulated below `F`. -/
theorem run_sim_fun (hE : EnvOk E) (himp : mod.imports = []) {k : Nat} {f : Function}
    (hf : mod.funcs[k]? = some f) {sigs : List (Option (List VT × Option VT))} {G : Nat}
    (hG : G = E.globals.length) {fd : function} (htr : trFunction sigs G f = some fd)
    {ps : List VT} {r : Option VT} (hsig : signatureOf f = some (ps, r))
    {CallOk : Nat → Prop} {F : Nat}
    (hC : ∀ k', CallOk k' → ∀ g, g < F → ∀ c : FCtx, c.sigs = sigs → CallSim A X E mod c g k')
    (hcalls : ∀ k', funId k' ∈ callees fd.fn_body → CallOk k') :
    RunSimFun A X E mod F k ps r fd := by
  intro α st args m env htyped hg hs
  obtain ⟨ps0, ls, r0, body, nc, hps, hls, hrs, hbody, hfd⟩ := trFunction_spec htr
  have hpr : ps0 = ps ∧ r0 = r := by
    unfold signatureOf at hsig
    rw [hps, hrs] at hsig
    cases r0 <;> simp at hsig <;> exact ⟨hsig.1, hsig.2⟩
  obtain ⟨rfl, rfl⟩ := hpr
  let c : FCtx := { locals := ps0 ++ ls, result := r0, nglobals := G, sigs := sigs }
  have hP := body_sim (c := c) (A := A) (X := X) (mod := mod) hE (by simp [c, hG])
    (fun k' hk' g hg => hC k' hk' g hg c rfl) F (Nat.le_refl _)
  have hnp : f.params.length = ps0.length := (mapM_length hps).symm
  have hnr : f.results.length = r0.toList.length := (mapM_length hrs).symm
  have hnl : f.locals.length = ls.length := (mapM_length hls).symm
  have hargs_len : ps0.length ≤ args.length := htyped.1
  have hvargs_len : (argVals ps0 args).length = ps0.length := by
    simp [argVals]; omega
  have hparams : fd.fn_params = (ps0.zipIdx).map fun x => (localId x.2, x.1.ty) := by rw [hfd]
  have htemps : fd.fn_temps =
      (ls.zipIdx).map (fun x => (localId (ps0.length + x.2), x.1.ty)) ++ bodyTemps body := by
    rw [hfd]
  -- Entry: the parameters, then the declared locals, then `brk`.
  obtain ⟨le1, hbind, hget1, -⟩ :=
    bind_params ps0 0 (argVals ps0 args) (create_undef_temps fd.fn_temps) hvargs_len
  have hentry : function_entry2 fd (argVals ps0 args) m empty_env le1 m := by
    refine .intro le1 (by rw [hfd]) ?_ ?_ (by rw [hparams]; exact hbind)
    · rw [hparams, var_names_params]
      exact List.Pairwise.map localId (fun a b hab e => hab (localId_inj e)) List.nodup_range'
    · intro x hx y hy hxy
      rw [hparams, var_names_params] at hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
      simp at hi
      rw [htemps] at hy
      simp only [var_names, List.map_append, List.mem_append, List.map_map, List.mem_map,
        Function.comp] at hy
      rcases hy with ⟨⟨t', j⟩, -, hj⟩ | ⟨y', hy', hyy⟩
      · simp only at hj
        have := localId_inj (hxy.trans hj.symm)
        omega
      · have := mem_bodyTemps hy'
        rw [hyy, ← hxy] at this
        exact this (by show (8 * i + 8 : Nat) % 8 = 0; omega)
  let le2 := setLocals le1 ps0.length (ls.zipIdx 0)
  let le3 := le2.insert brkId (.Vint (UInt32.ofNat 0))
  obtain ⟨hset2, hother2⟩ := setLocals_get le1 ps0.length ls 0
  have hinv : Inv E c [] st (f.toLocals ((args.take ps0.length).reverse)) le3 m := by
    refine { stack := trivial, locals := ?_, globals := hg, status := hs,
             brk := te_insert_same _ _ _ }
    refine ⟨by simp [Function.toLocals, c, hnl]; omega, ?_⟩
    intro i hi
    simp only [c, List.length_append] at hi
    by_cases hip : i < ps0.length
    · have hall : AllHas ps0 (args.take ps0.length).reverse := htyped.2
      obtain ⟨v, hv, ht⟩ := hall.get i hip
      refine ⟨v, ?_, ?_, ?_⟩
      · simp only [Function.toLocals]
        rw [List.getElem?_append_left (by simp; omega)]
        exact hv
      · simp only [c]
        rw [List.getElem_append_left hip]
        exact ht
      · rw [te_insert_ne _ (localId_ne_brkId i).symm,
          hother2 _ (fun j _ e => by have := localId_inj e; omega)]
        have h1 := hget1 i hip
        simp only [Nat.zero_add] at h1
        rw [h1]
        simp only [argVals, List.getElem?_map, hv]
        rfl
    · have hj : i - ps0.length < ls.length := by omega
      obtain ⟨t, ht, hl⟩ := hset2 (i - ps0.length) hj
      obtain ⟨t', ht', hl'⟩ := mapM_get hls (i - ps0.length) (by omega)
      rw [ht] at hl'
      cases hl'
      obtain ⟨hhas, hcval⟩ := VT.has_ofValueType ht'
      refine ⟨(f.locals[i - ps0.length]'(by omega)).zero, ?_, ?_, ?_⟩
      · simp only [Function.toLocals]
        rw [List.getElem?_append_right (by simp; omega)]
        simp only [List.length_reverse, List.length_take, Nat.min_eq_left hargs_len,
          List.getElem?_map]
        rw [List.getElem?_eq_getElem (by omega)]
        rfl
      · simp only [c]
        rw [List.getElem_append_right (by omega)]
        have : ls[i - ps0.length] = t := (List.getElem?_eq_some_iff.mp ht).2
        simp only [this]
        exact hhas
      · rw [te_insert_ne _ (localId_ne_brkId i).symm, hcval]
        rw [show i = ps0.length + 0 + (i - ps0.length) by omega]
        exact hl
  -- The body.
  have hcalls' : ∀ k', funId k' ∈ callees body → CallOk k' := fun k' hk => hcalls k' (by
    rw [hfd, callees_seqList]
    simp only [List.flatMap_append, List.mem_append, List.mem_flatMap]
    right
    refine ⟨wrapLoop body, by simp, ?_⟩
    simp [wrapLoop, callees, callees_seq_break, hk])
  have ho := hP [{ isLoop := false, base := 0, result := r0 }] [] r0.toList 0 f.body body nc hbody
    (Nat.le_refl _) (fun k l hl => by cases k <;> simp at hl; subst hl; exact Nat.le_refl _)
    hcalls' st _ le3 m env hinv
  -- The function's tail after the declared locals.
  let ret : statement := retStmt r0
  have hbodyEq : fd.fn_body = seqList ((ls.zipIdx).map (fun x => statement.Sset
      (localId (ps0.length + x.2)) x.1.zero) ++ [.Sset brkId (cint 0), wrapLoop body, ret]) := by
    rw [hfd]
  have hretEq : fd.fn_return = (r0.map VT.ty).getD .Tvoid := by rw [hfd]
  have hfun : ∀ {t le' m' out} vres,
      exec_stmt A X E.ge empty_env le3 m (.Ssequence (wrapLoop body) ret) t le' m' out →
      outcome_result_value out ((r0.map VT.ty).getD .Tvoid) vres m' →
      ∃ t', eval_funcall A X E.ge m (.Internal fd) (argVals ps0 args) t' m' vres := by
    intro t le' m' out vres hx hov
    have hx2 : exec_stmt A X E.ge empty_env le2 m
        (seqList [.Sset brkId (cint 0), wrapLoop body, ret]) (E0 ++ t) le' m' out :=
      .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sset _ _ _ _ _ _ (.eval_Econst_int _ _)) hx
    obtain ⟨t', hx3⟩ := exec_setLocals (A := A) (X := X) (ge := E.ge) ps0.length (ls.zipIdx 0) _
      (by simp) hx2
    rw [← hbodyEq] at hx3
    rw [← hretEq] at hov
    exact ⟨t', .eval_funcall_internal _ _ _ _ _ _ _ _ _ _ _ _ hentry hx3 hov
      (by rw [blocks_of_empty]; rfl)⟩
  -- The run.
  rw [run_eq (by simp [himp])]
  simp only [himp, List.length_nil, Nat.sub_zero, hf]
  simp only [Function.numParams, hnp, hnr]
  cases hres : exec F mod st (f.toLocals ((args.take ps0.length).reverse)) f.body env with
  | Fallthrough st' sl' =>
      rw [hres] at ho
      obtain ⟨σ'', hσ, -, t, le', m', hx, hinv', -⟩ := ho
      cases hσ
      obtain ⟨tw, hW⟩ := exec_wrap_exit hx (.inl rfl)
      cases r0 with
      | none =>
          obtain ⟨t', hcall⟩ := hfun .Vundef
            (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hW (.exec_Sreturn_none _ _ _)) rfl
          exact ⟨t', m', .Vundef, hcall, hinv'.globals, hinv'.status, by simp, rfl⟩
      | some t0 =>
          obtain ⟨v, vr, hvs, ht, hl, hrest⟩ := hinv'.stack.cons_inv
          have hret := exec_stmt.exec_Sreturn_some (A := A) (X := X) (ge := E.ge) empty_env le' m'
            (tmp 0 t0) (cval v) (.eval_Etempvar _ _ _ hl)
          obtain ⟨t', hcall⟩ := hfun (cval v) (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hW hret)
            (outcome_value ht m')
          have hvr : vr = [] := by cases vr <;> simp_all [StackRel]
          subst hvr
          exact ⟨t', m', cval v, hcall, hinv'.globals, hinv'.status, v, by simp [hvs], ht, rfl⟩
  | Break k st' sl' =>
      rw [hres] at ho
      obtain ⟨t, le', m', out, hx, hrel, -⟩ := ho
      cases k with
      | succ k => trivial
      | zero =>
          obtain ⟨l, hl, h0, hkept⟩ := hrel.target
          simp at hl; subst hl
          have hout : out = .Out_break := by simpa using h0 rfl
          subst hout
          obtain ⟨tw, hW⟩ := exec_wrap_exit hx (.inr rfl)
          cases r0 with
          | none =>
              obtain ⟨t', hcall⟩ := hfun .Vundef
                (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hW (.exec_Sreturn_none _ _ _)) rfl
              exact ⟨t', m', .Vundef, hcall, hrel.globals, hrel.status, by simp, rfl⟩
          | some t0 =>
              obtain ⟨v, hv, ht, hl⟩ := hkept rfl t0 rfl
              have hret := exec_stmt.exec_Sreturn_some (A := A) (X := X) (ge := E.ge) empty_env le'
                m' (tmp 0 t0) (cval v) (.eval_Etempvar _ _ _ hl)
              obtain ⟨t', hcall⟩ := hfun (cval v) (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hW hret)
                (outcome_value ht m')
              refine ⟨t', m', cval v, hcall, hrel.globals, hrel.status, v, ?_, ht, rfl⟩
              cases hsv : sl'.values with
              | nil => rw [hsv] at hv; simp at hv
              | cons w ws => rw [hsv] at hv; simp at hv; subst hv; simp
  | Return st' vs =>
      rw [hres] at ho
      obtain ⟨t, le', m', out, hx, hrel, hg', hs'⟩ := ho
      cases r0 with
      | none =>
          simp only [ReturnRel] at hrel
          subst hrel
          obtain ⟨t', hcall⟩ := hfun .Vundef
            (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ (exec_wrap_return hx) (by simp)) rfl
          exact ⟨t', m', .Vundef, hcall, hg', hs', by simp, rfl⟩
      | some t0 =>
          simp only [ReturnRel] at hrel
          obtain ⟨v, hv, ht, rfl⟩ := hrel
          obtain ⟨t', hcall⟩ := hfun (cval v)
            (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ (exec_wrap_return hx) (by simp)) (outcome_value ht m')
          refine ⟨t', m', cval v, hcall, hg', hs', v, ?_, ht, rfl⟩
          cases vs with
          | nil => simp at hv
          | cons w ws => simp at hv; subst hv; simp
  | Trap st' msg =>
      rw [hres] at ho
      obtain ⟨t, le', m', hx, hg', hs', hc⟩ := ho
      cases r0 with
      | none =>
          obtain ⟨t', hcall⟩ := hfun .Vundef
            (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ (exec_wrap_return hx) (by simp [trapOut])) rfl
          exact ⟨t', m', .Vundef, hcall, hg', hs', hc⟩
      | some t0 =>
          obtain ⟨t', hcall⟩ := hfun (zval t0)
            (.exec_Sseq_2 _ _ _ _ _ _ _ _ _ (exec_wrap_return hx) (by simp [trapOut]))
            (outcome_zero t0 m')
          exact ⟨t', m', zval t0, hcall, hg', hs', hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | ReturnCall _ _ _ => rw [hres] at ho; exact ho.elim
  | Throwing _ _ _ _ => rw [hres] at ho; exact ho.elim

end

end LeanExe.Native
