import LeanExe.Native.Clight.Run

/-!
The soundness of `run` against the big-step semantics: an `.ok` result of `exec_fn` or
`eval_funcall_fn` is an execution of `exec_stmt` or `eval_funcall`, for every semantics `X` of
external functions.  `run_sound` states it for a call from the initial memory, and
`run_program_sound` concludes `bigstep_program_terminates` from a result of `run_program`.  The
proofs go by induction on the fuel and, within one unit of fuel, by cases on the statement.
-/

namespace LClight

section Sound

variable {A : Archi} {X : ExtSem} {ge : genv}

theorem lvar_sound {e : env} {le : temp_env} {m : mem} {id : ident} {ty : type} {l : block}
    {ofs : ptrofs} (h : lvar ge e id ty = some (l, ofs)) :
    eval_lvalue A ge e le m (.Evar id ty) l ofs .Full := by
  unfold lvar at h
  cases he : e[id]? with
  | some p =>
      obtain ⟨l', ty'⟩ := p
      simp only [he] at h
      by_cases hty : ty' = ty
      · rw [ite_eq_left hty] at h
        cases h
        subst hty
        exact .eval_Evar_local _ _ _ he
      · rw [ite_eq_right hty] at h
        cases h
  | none =>
      simp only [he] at h
      cases hs : Genv.find_symbol ge id with
      | some l' =>
          simp only [hs] at h
          cases h
          exact .eval_Evar_global _ _ _ he hs
      | none =>
          simp only [hs] at h
          cases h

theorem deref_loc_fn_sound {ty : type} {m : mem} {l : block} {ofs : ptrofs} {v : val}
    (h : deref_loc_fn ty m l ofs = some v) : deref_loc ty m l ofs .Full v := by
  unfold deref_loc_fn at h
  cases hm : access_mode ty with
  | By_value chunk =>
      simp only [hm] at h
      exact .deref_loc_value chunk v hm h
  | By_reference =>
      simp only [hm] at h
      cases h
      exact .deref_loc_reference hm
  | By_copy => simp [hm] at h
  | By_nothing => simp [hm] at h

theorem assign_loc_fn_sound {ty : type} {m : mem} {b : block} {ofs : ptrofs} {bf : bitfield}
    {v : val} {m' : mem} (h : assign_loc_fn ty m b ofs bf v = some m') :
    assign_loc ty m b ofs bf v m' := by
  unfold assign_loc_fn at h
  cases bf with
  | Full =>
      cases hm : access_mode ty with
      | By_value chunk =>
          simp only [hm] at h
          exact .assign_loc_value v chunk m' hm h
      | By_reference => simp [hm] at h
      | By_copy => simp [hm] at h
      | By_nothing => simp [hm] at h
  | Bits _ _ _ _ => simp at h

/-- The value and the location of an expression, together, since `Eaddrof` of `Ederef b` needs
the location of `Ederef b`. -/
theorem eval_fn_sound (e : env) (le : temp_env) (m : mem) (a : expr) :
    (∀ v, eval_expr_fn A ge e le m a = some v → eval_expr A ge e le m a v) ∧
    (∀ l ofs bf, eval_lvalue_fn A ge e le m a = some (l, ofs, bf) →
      eval_lvalue A ge e le m a l ofs bf) := by
  induction a with
  | Econst_int i ty =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases h
      exact .eval_Econst_int i ty
  | Econst_float f ty =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases h
      exact .eval_Econst_float f ty
  | Econst_single f ty =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases h
      exact .eval_Econst_single f ty
  | Econst_long i ty =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases h
      exact .eval_Econst_long i ty
  | Evar id ty =>
      refine ⟨fun v h => ?_, fun l ofs bf h => ?_⟩
      · simp only [eval_expr_fn] at h
        cases hl : lvar ge e id ty with
        | none => simp [hl] at h
        | some p =>
            obtain ⟨l, ofs⟩ := p
            simp only [hl] at h
            exact .eval_Elvalue _ l ofs .Full v (lvar_sound hl) (deref_loc_fn_sound h)
      · simp only [eval_lvalue_fn] at h
        cases hl : lvar ge e id ty with
        | none => simp [hl] at h
        | some p =>
            obtain ⟨l', ofs'⟩ := p
            simp only [hl] at h
            cases h
            exact lvar_sound hl
  | Etempvar id ty =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      exact .eval_Etempvar id ty v h
  | Ederef a ty iha =>
      refine ⟨fun v h => ?_, fun l ofs bf h => ?_⟩
      · simp only [eval_expr_fn] at h
        cases ha : eval_expr_fn A ge e le m a with
        | none => simp [ha] at h
        | some va =>
            cases va with
            | Vptr l ofs =>
                simp only [ha] at h
                exact .eval_Elvalue _ l ofs .Full v (.eval_Ederef a ty l ofs (iha.1 _ ha))
                  (deref_loc_fn_sound h)
            | _ => simp [ha] at h
      · simp only [eval_lvalue_fn] at h
        cases ha : eval_expr_fn A ge e le m a with
        | none => simp [ha] at h
        | some va =>
            cases va with
            | Vptr l' ofs' =>
                simp only [ha] at h
                cases h
                exact .eval_Ederef a ty _ _ (iha.1 _ ha)
            | _ => simp [ha] at h
  | Eaddrof a ty iha =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      cases a with
      | Evar id ty' =>
          simp only [eval_expr_fn] at h
          cases hl : lvar ge e id ty' with
          | none => simp [hl] at h
          | some p =>
              obtain ⟨l, ofs⟩ := p
              simp only [hl] at h
              cases h
              exact .eval_Eaddrof _ ty l ofs (lvar_sound hl)
      | Ederef b ty' =>
          simp only [eval_expr_fn] at h
          cases hb : eval_expr_fn A ge e le m b with
          | none => simp [hb] at h
          | some vb =>
              cases vb with
              | Vptr l ofs =>
                  simp only [hb] at h
                  cases h
                  exact .eval_Eaddrof _ ty l ofs (iha.2 l ofs .Full (by simp [eval_lvalue_fn, hb]))
              | _ => simp [hb] at h
      | _ => simp [eval_expr_fn] at h
  | Eunop op a ty iha =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases ha : eval_expr_fn A ge e le m a with
      | none => simp [ha] at h
      | some v1 =>
          simp only [ha] at h
          exact .eval_Eunop op a ty v1 v (iha.1 _ ha) h
  | Ebinop op a1 a2 ty ih1 ih2 =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases h1 : eval_expr_fn A ge e le m a1 with
      | none => simp [h1] at h
      | some v1 =>
          cases h2 : eval_expr_fn A ge e le m a2 with
          | none => simp [h1, h2] at h
          | some v2 =>
              simp only [h1, h2] at h
              exact .eval_Ebinop op a1 a2 ty v1 v2 v (ih1.1 _ h1) (ih2.1 _ h2) h
  | Ecast a ty iha =>
      refine ⟨fun v h => ?_, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
      simp only [eval_expr_fn] at h
      cases ha : eval_expr_fn A ge e le m a with
      | none => simp [ha] at h
      | some v1 =>
          simp only [ha] at h
          exact .eval_Ecast a ty v1 v (iha.1 _ ha) h
  | Efield a f ty _ =>
      exact ⟨fun v h => by simp [eval_expr_fn] at h, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
  | Esizeof ty1 ty =>
      exact ⟨fun v h => by simp [eval_expr_fn] at h, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩
  | Ealignof ty1 ty =>
      exact ⟨fun v h => by simp [eval_expr_fn] at h, fun l ofs bf h => by simp [eval_lvalue_fn] at h⟩

theorem eval_expr_fn_sound {e : env} {le : temp_env} {m : mem} {a : expr} {v : val}
    (h : eval_expr_fn A ge e le m a = some v) : eval_expr A ge e le m a v :=
  (eval_fn_sound e le m a).1 v h

theorem eval_lvalue_fn_sound {e : env} {le : temp_env} {m : mem} {a : expr} {l : block}
    {ofs : ptrofs} {bf : bitfield} (h : eval_lvalue_fn A ge e le m a = some (l, ofs, bf)) :
    eval_lvalue A ge e le m a l ofs bf :=
  (eval_fn_sound e le m a).2 l ofs bf h

theorem eval_exprlist_fn_sound {e : env} {le : temp_env} {m : mem} :
    ∀ (al : List expr) (tyl : List type) (vl : List val),
      eval_exprlist_fn A ge e le m al tyl = some vl → eval_exprlist A ge e le m al tyl vl
  | [], [], vl, h => by
      simp only [eval_exprlist_fn] at h
      cases h
      exact .eval_Enil
  | a :: bl, ty :: tyl, vl, h => by
      simp only [eval_exprlist_fn] at h
      cases h1 : eval_expr_fn A ge e le m a with
      | none => simp [h1] at h
      | some v1 =>
          cases h2 : sem_cast v1 (typeof a) ty m with
          | none => simp [h1, h2] at h
          | some v2 =>
              cases h3 : eval_exprlist_fn A ge e le m bl tyl with
              | none => simp [h1, h2, h3] at h
              | some vl' =>
                  simp only [h1, h2, h3] at h
                  cases h
                  exact .eval_Econs a bl ty tyl v1 v2 vl' (eval_expr_fn_sound h1) h2
                    (eval_exprlist_fn_sound bl tyl vl' h3)
  | [], _ :: _, vl, h => by simp [eval_exprlist_fn] at h
  | _ :: _, [], vl, h => by simp [eval_exprlist_fn] at h

theorem invert_symbol_fn_sound {b : block} {id : ident} (h : invert_symbol_fn ge b = some id) :
    Genv.find_symbol ge id = some b := by
  unfold invert_symbol_fn at h
  cases hf : ge.genv_symb.toList.find? (fun e => e.2 == b) with
  | none => simp [hf] at h
  | some e =>
      simp only [hf, Option.map_some, Option.some.injEq] at h
      subst h
      have hb : e.2 = b := by simpa using List.find?_some hf
      have hmem : (e.1, e.2) ∈ ge.genv_symb.toList := List.mem_of_find?_eq_some hf
      rw [Std.TreeMap.mem_toList_iff_getElem?_eq_some] at hmem
      simp only [Genv.find_symbol, hmem, hb]

theorem eventval_of_val_sound {v : val} {ty : typ} {ev : eventval}
    (h : eventval_of_val v ty = some ev) : eventval_match ev ty v := by
  cases v <;> cases ty <;> simp [eventval_of_val] at h <;> subst h <;> constructor

theorem external_call_fn_sound {ef : external_function} {vargs : List val} {m : mem}
    {t : trace} {vres : val} {m' : mem}
    (h : external_call_fn A ge ef vargs m = some (t, vres, m')) :
    external_call A X ef ge vargs m t vres m' := by
  unfold external_call_fn at h
  cases ef with
  | EF_builtin name sg =>
      cases hb : lookup_builtin_function name sg with
      | none => simp [hb] at h
      | some bf =>
          cases hs : builtin_function_sem A bf vargs with
          | none => simp [hb, hs] at h
          | some vres' =>
              simp only [hb, hs] at h
              cases h
              simp only [external_call, hb]
              exact ⟨hs, rfl, rfl⟩
  | EF_vstore chunk =>
      match vargs, h with
      | [.Vptr b ofs, v], h =>
          simp only [external_call]
          by_cases hv : Genv.block_is_volatile ge b = true
          · simp only [hv, ite_true] at h
            cases hi : invert_symbol_fn ge b with
            | none => simp [hi] at h
            | some id =>
                cases he : eventval_of_val (Val.load_result chunk v) (type_of_chunk chunk) with
                | none => simp [hi, he] at h
                | some ev =>
                    simp only [hi, he, Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl, rfl⟩ := h
                    exact .volatile_store_sem_intro b ofs m v _ m
                      (.volatile_store_vol chunk m b ofs id ev v hv (invert_symbol_fn_sound hi)
                        (eventval_of_val_sound he))
          · have hv' : Genv.block_is_volatile ge b = false := by simpa using hv
            simp only [hv', Bool.false_eq_true, ite_false] at h
            cases hs : Mem.storev chunk m (.Vptr b ofs) v with
            | none => simp [hs] at h
            | some m1 =>
                simp only [hs, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                exact .volatile_store_sem_intro b ofs m v _ m1
                  (.volatile_store_nonvol chunk m b ofs v m1 hv' hs)
      | [], h => simp at h
      | [.Vptr _ _], h => simp at h
      | .Vptr _ _ :: _ :: _ :: _, h => simp at h
      | .Vundef :: _, h => simp at h
      | .Vint _ :: _, h => simp at h
      | .Vlong _ :: _, h => simp at h
      | .Vfloat _ :: _, h => simp at h
      | .Vsingle _ :: _, h => simp at h
  | _ => simp at h

theorem function_entry2_fn_sound {f : function} {vargs : List val} {le : temp_env} {m : mem}
    (h : function_entry2_fn f vargs = some le) : function_entry2 f vargs m empty_env le m := by
  unfold function_entry2_fn at h
  by_cases hc : f.fn_vars = [] ∧ (var_names f.fn_params).Nodup ∧
      (∀ x ∈ var_names f.fn_params, ∀ y ∈ var_names f.fn_temps, x ≠ y)
  · rw [ite_eq_left hc] at h
    exact .intro le hc.1 hc.2.1 hc.2.2 h
  · rw [ite_eq_right hc] at h
    cases h

theorem outcome_result_value_fn_sound {out : outcome} {t : type} {m : mem} {v : val}
    (h : outcome_result_value_fn out t m = some v) : outcome_result_value out t v m := by
  cases out with
  | Out_normal =>
      cases t with
      | Tvoid =>
          simp only [outcome_result_value_fn] at h
          cases h
          exact rfl
      | _ => simp [outcome_result_value_fn] at h
  | Out_return r =>
      cases r with
      | none =>
          cases t with
          | Tvoid =>
              simp only [outcome_result_value_fn] at h
              cases h
              exact rfl
          | _ => simp [outcome_result_value_fn] at h
      | some p =>
          obtain ⟨v', t'⟩ := p
          simp only [outcome_result_value_fn] at h
          by_cases hv : t = .Tvoid
          · rw [ite_eq_left hv] at h
            cases h
          · rw [ite_eq_right hv] at h
            exact ⟨hv, h⟩
  | Out_break => simp [outcome_result_value_fn] at h
  | Out_continue => simp [outcome_result_value_fn] at h

theorem fn_sound (fuel : Nat) :
    (∀ e le m s t le' m' out, exec_fn A ge fuel e le m s = .ok (t, le', m', out) →
      exec_stmt A X ge e le m s t le' m' out) ∧
    (∀ m fd vargs t m' vres, eval_funcall_fn A ge fuel m fd vargs = .ok (t, m', vres) →
      eval_funcall A X ge m fd vargs t m' vres) := by
  induction fuel with
  | zero =>
      exact ⟨fun _ _ _ _ _ _ _ _ h => by simp [exec_fn] at h,
        fun _ _ _ _ _ _ h => by simp [eval_funcall_fn] at h⟩
  | succ fuel ih =>
    obtain ⟨ihs, ihf⟩ := ih
    refine ⟨fun e le m s t le' m' out h => ?_, fun m fd vargs t m' vres h => ?_⟩
    · cases s with
      | Sskip =>
          simp only [exec_fn] at h
          cases h
          exact .exec_Sskip e le m
      | Sassign a1 a2 =>
          simp only [exec_fn] at h
          cases hl : eval_lvalue_fn A ge e le m a1 with
          | none => simp [hl] at h
          | some p =>
              obtain ⟨loc, ofs, bf⟩ := p
              cases hv : eval_expr_fn A ge e le m a2 with
              | none => simp [hl, hv] at h
              | some v2 =>
                  cases hc : sem_cast v2 (typeof a2) (typeof a1) m with
                  | none => simp [hl, hv, hc] at h
                  | some v =>
                      cases ha : assign_loc_fn (typeof a1) m loc ofs bf v with
                      | none => simp [hl, hv, hc, ha] at h
                      | some m'' =>
                          simp only [hl, hv, hc, ha] at h
                          cases h
                          exact .exec_Sassign e le m a1 a2 loc ofs bf v2 v _
                            (eval_lvalue_fn_sound hl) (eval_expr_fn_sound hv) hc
                            (assign_loc_fn_sound ha)
      | Sset id a =>
          simp only [exec_fn] at h
          cases hv : eval_expr_fn A ge e le m a with
          | none => simp [hv] at h
          | some v =>
              simp only [hv] at h
              cases h
              exact .exec_Sset e le m id a v (eval_expr_fn_sound hv)
      | Scall optid a al =>
          simp only [exec_fn] at h
          cases hcf : classify_fun (typeof a) with
          | fun_default => simp [hcf] at h
          | fun_case_f tyargs tyres cconv =>
              cases hvf : eval_expr_fn A ge e le m a with
              | none => simp [hcf, hvf] at h
              | some vf =>
                  cases hva : eval_exprlist_fn A ge e le m al tyargs with
                  | none => simp [hcf, hvf, hva] at h
                  | some vargs =>
                      cases hf : Genv.find_funct ge vf with
                      | none => simp [hcf, hvf, hva, hf] at h
                      | some f =>
                          simp only [hcf, hvf, hva, hf] at h
                          by_cases hty : type_of_fundef f = .Tfunction tyargs tyres cconv
                          · rw [ite_eq_left hty] at h
                            cases hc : eval_funcall_fn A ge fuel m f vargs with
                            | error err => simp [hc] at h
                            | ok r =>
                                obtain ⟨t0, m0, vres⟩ := r
                                simp only [hc] at h
                                cases h
                                exact .exec_Scall e le m optid a al tyargs tyres cconv vf vargs f _
                                  _ vres hcf (eval_expr_fn_sound hvf)
                                  (eval_exprlist_fn_sound _ _ _ hva) hf hty
                                  (ihf _ _ _ _ _ _ hc)
                          · rw [ite_eq_right hty] at h
                            cases h
      | Sbuiltin optid ef tyargs al =>
          simp only [exec_fn] at h
          cases hv : eval_exprlist_fn A ge e le m al tyargs with
          | none => simp [hv] at h
          | some vargs =>
              cases hx : external_call_fn A ge ef vargs m with
              | none => simp [hv, hx] at h
              | some r =>
                  obtain ⟨t0, vres, m0⟩ := r
                  simp only [hv, hx] at h
                  cases h
                  exact .exec_Sbuiltin e le m optid ef al tyargs vargs _ _ vres
                    (eval_exprlist_fn_sound _ _ _ hv) (external_call_fn_sound hx)
      | Ssequence s1 s2 =>
          simp only [exec_fn] at h
          cases h1 : exec_fn A ge fuel e le m s1 with
          | error err => simp [h1] at h
          | ok r1 =>
              obtain ⟨t1, le1, m1, out1⟩ := r1
              have d1 := ihs _ _ _ _ _ _ _ _ h1
              cases out1 with
              | Out_normal =>
                  simp only [h1] at h
                  cases h2 : exec_fn A ge fuel e le1 m1 s2 with
                  | error err => simp [h2] at h
                  | ok r2 =>
                      obtain ⟨t2, le2, m2, out2⟩ := r2
                      simp only [h2] at h
                      cases h
                      exact .exec_Sseq_1 e le m s1 s2 t1 le1 m1 t2 _ _ _ d1
                        (ihs _ _ _ _ _ _ _ _ h2)
              | Out_break =>
                  simp only [h1] at h
                  cases h
                  exact .exec_Sseq_2 e le m s1 s2 _ _ _ .Out_break d1 (by intro hn; cases hn)
              | Out_continue =>
                  simp only [h1] at h
                  cases h
                  exact .exec_Sseq_2 e le m s1 s2 _ _ _ .Out_continue d1
                    (by intro hn; cases hn)
              | Out_return ov =>
                  simp only [h1] at h
                  cases h
                  exact .exec_Sseq_2 e le m s1 s2 _ _ _ (.Out_return ov) d1
                    (by intro hn; cases hn)
      | Sifthenelse a s1 s2 =>
          simp only [exec_fn] at h
          cases hv : eval_expr_fn A ge e le m a with
          | none => simp [hv] at h
          | some v1 =>
              cases hb : bool_val v1 (typeof a) m with
              | none => simp [hv, hb] at h
              | some b =>
                  simp only [hv, hb] at h
                  exact .exec_Sifthenelse e le m a s1 s2 v1 b t le' m' out (eval_expr_fn_sound hv)
                    hb (ihs _ _ _ _ _ _ _ _ h)
      | Sloop s1 s2 =>
          simp only [exec_fn] at h
          cases h1 : exec_fn A ge fuel e le m s1 with
          | error err => simp [h1] at h
          | ok r1 =>
              obtain ⟨t1, le1, m1, out1⟩ := r1
              have d1 := ihs _ _ _ _ _ _ _ _ h1
              cases out1 with
              | Out_break =>
                  simp only [h1] at h
                  cases h
                  exact .exec_Sloop_stop1 e le m s1 s2 _ _ _ .Out_break .Out_normal d1
                    .Out_break_or_return_B
              | Out_return ov =>
                  simp only [h1] at h
                  cases h
                  exact .exec_Sloop_stop1 e le m s1 s2 _ _ _ (.Out_return ov) (.Out_return ov)
                    d1 (.Out_break_or_return_R ov)
              | Out_normal =>
                  simp only [h1] at h
                  cases h2 : exec_fn A ge fuel e le1 m1 s2 with
                  | error err => simp [h2] at h
                  | ok r2 =>
                      obtain ⟨t2, le2, m2, out2⟩ := r2
                      have d2 := ihs _ _ _ _ _ _ _ _ h2
                      cases out2 with
                      | Out_normal =>
                          simp only [h2] at h
                          cases h3 : exec_fn A ge fuel e le2 m2 (.Sloop s1 s2) with
                          | error err => simp [h3] at h
                          | ok r3 =>
                              obtain ⟨t3, le3, m3, out3⟩ := r3
                              simp only [h3] at h
                              cases h
                              exact .exec_Sloop_loop e le m s1 s2 t1 le1 m1 .Out_normal t2 le2 m2
                                t3 _ _ _ d1 .Out_normal_or_continue_N d2
                                (ihs _ _ _ _ _ _ _ _ h3)
                      | Out_break =>
                          simp only [h2] at h
                          cases h
                          exact .exec_Sloop_stop2 e le m s1 s2 t1 le1 m1 .Out_normal t2 _ _
                            .Out_break .Out_normal d1 .Out_normal_or_continue_N d2
                            .Out_break_or_return_B
                      | Out_return ov =>
                          simp only [h2] at h
                          cases h
                          exact .exec_Sloop_stop2 e le m s1 s2 t1 le1 m1 .Out_normal t2 _ _
                            (.Out_return ov) (.Out_return ov) d1 .Out_normal_or_continue_N d2
                            (.Out_break_or_return_R ov)
                      | Out_continue => simp [h2] at h
              | Out_continue =>
                  simp only [h1] at h
                  cases h2 : exec_fn A ge fuel e le1 m1 s2 with
                  | error err => simp [h2] at h
                  | ok r2 =>
                      obtain ⟨t2, le2, m2, out2⟩ := r2
                      have d2 := ihs _ _ _ _ _ _ _ _ h2
                      cases out2 with
                      | Out_normal =>
                          simp only [h2] at h
                          cases h3 : exec_fn A ge fuel e le2 m2 (.Sloop s1 s2) with
                          | error err => simp [h3] at h
                          | ok r3 =>
                              obtain ⟨t3, le3, m3, out3⟩ := r3
                              simp only [h3] at h
                              cases h
                              exact .exec_Sloop_loop e le m s1 s2 t1 le1 m1 .Out_continue t2 le2
                                m2 t3 _ _ _ d1 .Out_normal_or_continue_C d2
                                (ihs _ _ _ _ _ _ _ _ h3)
                      | Out_break =>
                          simp only [h2] at h
                          cases h
                          exact .exec_Sloop_stop2 e le m s1 s2 t1 le1 m1 .Out_continue t2 _ _
                            .Out_break .Out_normal d1 .Out_normal_or_continue_C d2
                            .Out_break_or_return_B
                      | Out_return ov =>
                          simp only [h2] at h
                          cases h
                          exact .exec_Sloop_stop2 e le m s1 s2 t1 le1 m1 .Out_continue t2 _ _
                            (.Out_return ov) (.Out_return ov) d1 .Out_normal_or_continue_C d2
                            (.Out_break_or_return_R ov)
                      | Out_continue => simp [h2] at h
      | Sbreak =>
          simp only [exec_fn] at h
          cases h
          exact .exec_Sbreak e le m
      | Scontinue =>
          simp only [exec_fn] at h
          cases h
          exact .exec_Scontinue e le m
      | Sreturn oa =>
          cases oa with
          | none =>
              simp only [exec_fn] at h
              cases h
              exact .exec_Sreturn_none e le m
          | some a =>
              simp only [exec_fn] at h
              cases hv : eval_expr_fn A ge e le m a with
              | none => simp [hv] at h
              | some v =>
                  simp only [hv] at h
                  cases h
                  exact .exec_Sreturn_some e le m a v (eval_expr_fn_sound hv)
      | Sswitch _ _ => simp [exec_fn] at h
      | Slabel _ _ => simp [exec_fn] at h
      | Sgoto _ => simp [exec_fn] at h
    · cases fd with
      | Internal f =>
          simp only [eval_funcall_fn] at h
          cases he : function_entry2_fn f vargs with
          | none => simp [he] at h
          | some le1 =>
              cases hb : exec_fn A ge fuel empty_env le1 m f.fn_body with
              | error err => simp [he, hb] at h
              | ok r =>
                  obtain ⟨t0, le2, m2, out⟩ := r
                  cases hr : outcome_result_value_fn out f.fn_return m2 with
                  | none => simp [he, hb, hr] at h
                  | some vres0 =>
                      cases hfl : Mem.free_list m2 (blocks_of_env empty_env) with
                      | none => simp [he, hb, hr, hfl] at h
                      | some m3 =>
                          simp only [he, hb, hr, hfl] at h
                          cases h
                          exact .eval_funcall_internal m f vargs _ empty_env le1 le2 m m2 out
                            _ _ (function_entry2_fn_sound he) (ihs _ _ _ _ _ _ _ _ hb)
                            (outcome_result_value_fn_sound hr) hfl
      | External ef targs tres cconv =>
          simp only [eval_funcall_fn] at h
          cases hx : external_call_fn A ge ef vargs m with
          | none => simp [hx] at h
          | some r =>
              obtain ⟨t0, vres0, m0⟩ := r
              simp only [hx] at h
              cases h
              exact .eval_funcall_external m ef targs tres cconv vargs _ _ _
                (external_call_fn_sound hx)

theorem exec_fn_sound {fuel : Nat} {e : env} {le : temp_env} {m : mem} {s : statement}
    {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
    (h : exec_fn A ge fuel e le m s = .ok (t, le', m', out)) :
    exec_stmt A X ge e le m s t le' m' out :=
  (fn_sound fuel).1 _ _ _ _ _ _ _ _ h

theorem eval_funcall_fn_sound {fuel : Nat} {m : mem} {fd : fundef function} {vargs : List val}
    {t : trace} {m' : mem} {vres : val}
    (h : eval_funcall_fn A ge fuel m fd vargs = .ok (t, m', vres)) :
    eval_funcall A X ge m fd vargs t m' vres :=
  (fn_sound fuel).2 _ _ _ _ _ _ h

end Sound

/-- A result of `run` is a call, in the big-step semantics, of the function that `name` denotes,
from the program's initial memory. -/
theorem run_sound {A : Archi} {X : ExtSem} {p : program function} {name : ident}
    {args : List val} {fuel : Nat} {t : trace} {m : mem} {vres : val}
    (h : run A p name args fuel = .ok (t, m, vres)) :
    ∃ m0 b fd, init_mem p = some m0 ∧ Genv.find_symbol (globalenv p) name = some b ∧
      Genv.find_funct_ptr (globalenv p) b = some fd ∧
      eval_funcall A X (globalenv p) m0 fd args t m vres := by
  unfold run at h
  cases hm : init_mem p with
  | none => simp [hm] at h
  | some m0 =>
      cases hs : Genv.find_symbol (globalenv p) name with
      | none => simp [hm, hs] at h
      | some b =>
          cases hf : Genv.find_funct_ptr (globalenv p) b with
          | none => simp [hm, hs, hf] at h
          | some fd =>
              simp only [hm, hs, hf] at h
              exact ⟨m0, b, fd, rfl, rfl, hf, eval_funcall_fn_sound h⟩

/-- A result of `run_program` is an execution of the whole program, as
`bigstep_program_terminates` states it. -/
theorem run_program_sound {A : Archi} {X : ExtSem} {p : program function} {fuel : Nat}
    {t : trace} {r : int} (h : run_program A p fuel = .ok (t, r)) :
    bigstep_program_terminates A X p t r := by
  unfold run_program at h
  cases hm : init_mem p with
  | none => simp [hm] at h
  | some m0 =>
      cases hs : Genv.find_symbol (globalenv p) p.prog_main with
      | none => simp [hm, hs] at h
      | some b =>
          cases hf : Genv.find_funct_ptr (globalenv p) b with
          | none => simp [hm, hs, hf] at h
          | some fd =>
              simp only [hm, hs, hf] at h
              by_cases hty : type_of_fundef fd = .Tfunction [] type_int32s cc_default
              · rw [ite_eq_left hty] at h
                cases he : eval_funcall_fn A (globalenv p) fuel m0 fd [] with
                | error err => simp [he] at h
                | ok res =>
                    obtain ⟨t0, m1, v⟩ := res
                    cases v with
                    | Vint r0 =>
                        simp only [he, Except.ok.injEq, Prod.mk.injEq] at h
                        obtain ⟨rfl, rfl⟩ := h
                        exact .bigstep_program_terminates_intro b fd m0 m1 _ _ hm hs hf hty
                          (eval_funcall_fn_sound he)
                    | _ => simp [he] at h
              · rw [ite_eq_right hty] at h
                cases h

end LClight
