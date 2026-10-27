import LeanExe.Native.Proof.Branches

/-!
The simulation of `call`.  `CallSim g k` states what a call of function `k` at fuel `g` needs:
the function's block and translation in the global environment, and the relation between
Talos's `run` and CompCert's `eval_funcall` for it, `RunOutcome`.
-/

namespace LeanExe.Native

open Wasm LClight

/-- The C arguments of a call with parameters `ps` from the Talos stack `args`, top first: the
top `ps.length` values, deepest first. -/
def argVals (ps : List VT) (args : List Value) : List val :=
  ((args.take ps.length).reverse).map cval

/-- The arguments have the parameters' types. -/
def ArgsTyped (ps : List VT) (args : List Value) : Prop :=
  ps.length ≤ args.length ∧ AllHas ps (args.take ps.length).reverse

/-- Talos's results `vs` over the caller's remaining stack `rest`, and the C result `vres` with
the memory `m` after the call: with several results, `vres` is undefined and the result globals
hold the results. -/
def ResultRel (E : Env) (rs : List VT) (vs rest : List Value) (vres : val) (m : mem) : Prop :=
  match rs with
  | [] => vs = rest ∧ vres = .Vundef
  | [t] => ∃ v, vs = v :: rest ∧ t.has v = true ∧ vres = cval v
  | rs => ∃ ws, vs = ws ++ rest ∧ ws.length = rs.length ∧ vres = .Vundef ∧ ResultsIn E rs ws m

section

variable (A : Archi) (X : ExtSem) (E : Env) (mod : Module)

/-- The C call of `fd` from `m` with the arguments of `args` does what Talos's `res` says. -/
def RunOutcome (ps : List VT) (rs : List VT) (fd : function) {α : Type} (res : Result α)
    (args : List Value) (m : mem) : Prop :=
  match res with
  | .Success vs st' => ∃ t m' vres,
      eval_funcall A X E.ge m (.Internal fd) (argVals ps args) t m' vres ∧
      StoreRel E st' m' ∧ StatusRel E m' 0 ∧
      ResultRel E rs vs (args.drop ps.length) vres m'
  | .Trap st' msg => ∃ t m' vres,
      eval_funcall A X E.ge m (.Internal fd) (argVals ps args) t m' vres ∧
      StoreRel E st' m' ∧ StatusRel E m' (trapCode msg) ∧ trapCode msg ≠ 0
  | .Invalid _ => True
  | .OutOfFuel => True
  | .Thrown _ _ _ => False

/-- The simulation of a call of function `k`, whose C translation is `fd`, at fuel `g`. -/
def RunSimFun (g k : Nat) (ps : List VT) (rs : List VT) (fd : function) : Prop :=
  ∀ {α : Type} (st : Store α) (args : List Value) (m : mem) (env : HostEnv α),
    ArgsTyped ps args → StoreRel E st m → StatusRel E m 0 →
    RunOutcome A X E ps rs fd (run g mod k st args env) args m

/-- What a call of function `k` needs at fuel `g`, for a caller whose context is `c`. -/
def CallSim (c : FCtx) (g k : Nat) : Prop :=
  ∃ ps rs b fd, (c.sigs[k]?).join = some (ps, rs) ∧ Genv.find_symbol E.ge (funId k) = some b ∧
    Genv.find_funct_ptr E.ge b = some (.Internal fd) ∧ type_of_function fd = funType ps rs ∧
    ResOk E rs ∧ RunSimFun A X E mod g k ps rs fd

end

theorem tr_call {c : FCtx} {L : List Label} {σ : List VT} {n k : Nat} {s : statement}
    {σ' : Option (List VT)} {n' : Nat} (h : trInstr c L σ n (.call k) = some (s, σ', n')) :
    ∃ (ps rs σr : List VT), (c.sigs[k]?).join = some (ps, rs) ∧
      σ = ps.reverse ++ σr ∧
      curBase L ≤ σr.length ∧
      ((rs = [] ∧ σ' = some σr ∧ n' = n ∧
          s = .Ssequence (.Scall none (.Evar (funId k) (funType ps rs)) (callArgs σr.length ps))
            (statusCheck c.result)) ∨
        (∃ t, rs = [t] ∧ σ' = some (t :: σr) ∧ n' = n + 1 ∧
          s = .Ssequence
            (.Ssequence (.Scall (some (callId n)) (.Evar (funId k) (funType ps rs))
                (callArgs σr.length ps))
              (.Sset (slotId σr.length t) (.Etempvar (callId n) t.ty)))
            (statusCheck c.result)) ∨
        (2 ≤ rs.length ∧ σ' = some (rs.reverse ++ σr) ∧ n' = n ∧
          s = .Ssequence
            (.Ssequence (.Scall none (.Evar (funId k) (funType ps rs)) (callArgs σr.length ps))
              (seqList (resLoads rs 0 σr.length)))
            (statusCheck c.result))) := by
  simp [trInstr, pops, Option.bind_eq_some_iff] at h
  obtain ⟨ps, rs, hsig, hb, htake, hm⟩ := h
  have hσ : σ = ps.reverse ++ σ.drop ps.length := by
    rw [← htake, List.take_append_drop]
  have hlen : σ.length - ps.length = (σ.drop ps.length).length := by simp
  refine ⟨ps, rs, σ.drop ps.length, hsig, hσ, by simp; omega, ?_⟩
  rw [hlen] at hm
  rcases rs with _ | ⟨t, _ | ⟨t2, rs⟩⟩
  · simp at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact .inl ⟨rfl, rfl, rfl, by rw [List.length_drop]⟩
  · simp at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact .inr (.inl ⟨t, rfl, rfl, rfl, by rw [List.length_drop]⟩)
  · simp at hm
    obtain ⟨rfl, rfl, rfl⟩ := hm
    exact .inr (.inr ⟨by simp, by simp, rfl, by rw [List.length_drop]⟩)

theorem ArgsRel.eval {A : Archi} {ge : genv} {le : temp_env} {m : mem} {base : Nat}
    {ps : List VT} {vs : List Value} (h : ArgsRel le base ps vs) :
    eval_exprlist A ge empty_env le m (callArgs base ps) (ps.map VT.ty) (vs.map cval) := by
  induction ps generalizing base vs with
  | nil =>
      cases vs <;> simp_all [ArgsRel, callArgs]
      exact .eval_Enil
  | cons p ps ih =>
      cases vs with
      | nil => simp [ArgsRel] at h
      | cons v vs =>
          exact .eval_Econs _ _ _ _ _ _ _ (.eval_Etempvar _ _ _ h.2.1) (cast_cval h.1 m)
            (ih h.2.2)

theorem trapCode_le (msg : String) : trapCode msg ≤ 3 := by
  unfold trapCode
  split
  · decide
  · split
    · decide
    · split <;> decide

section

variable {A : Archi} {X : ExtSem} {E : Env} {mod : Module} {c : FCtx}

/-- The test after a call when `lx_status` is `code`. -/
theorem exec_statusCheck {le : temp_env} {m : mem} {code : Nat} (hE : EnvOk E)
    (h : StatusRel E m code) (hcode : code ≤ 3) (r : Option VT) :
    exec_stmt A X E.ge empty_env le m (statusCheck r) E0 le m
      (if code = 0 then .Out_normal else trapOut r) := by
  have hc : eval_expr A E.ge empty_env le m (.Ebinop .One (.Evar statusId tuint) (cint 0) tint)
      (.Vint (if code ≠ 0 then 1 else 0)) := by
    refine .eval_Ebinop _ _ _ _ _ _ _ (eval_global_int hE.status h.1) (.eval_Econst_int _ _) ?_
    show sem_binary_operation A .One (.Vint (UInt32.ofNat code)) tuint (.Vint (UInt32.ofNat 0))
      tuint m = _
    rw [sem_ne_ii]
    by_cases h0 : code = 0
    · subst h0; simp
    · have : UInt32.ofNat code ≠ 0 := fun e =>
        h0 ((uint32_ofNat_eq_zero (by omega)).mp e)
      simp [this, h0]
  by_cases h0 : code = 0
  · subst h0
    refine .exec_Sifthenelse _ _ _ _ _ _ _ false _ _ _ _ hc ?_ (by simpa using .exec_Sskip _ _ _)
    show bool_val _ tint m = _
    simpa using bool_int m 0
  · refine .exec_Sifthenelse _ _ _ _ _ _ _ true _ _ _ _ hc ?_ ?_
    · show bool_val _ tint m = _
      simpa [h0] using bool_int m 1
    · simpa [h0] using exec_retZero A X E.ge le m r

theorem sim_call (hE : EnvOk E) {CallOk : Nat → Prop} (f k : Nat)
    (hok : CallOk k → CallSim A X E mod c f k) :
    InstrSimL A X E mod c CallOk (f + 1) (.call k) := by
  intro L σ n s σ' n' htr hbase hL hcalls α st sl le m env hinv
  obtain ⟨ps, rs, σr, hsig, rfl, hb, hcase⟩ := tr_call htr
  have hk : CallOk k := hcalls k (by
    rcases hcase with ⟨-, -, -, rfl⟩ | ⟨t, -, -, -, rfl⟩ | ⟨-, -, -, rfl⟩ <;> simp [callees])
  obtain ⟨ps', rs', b, fd, hsig', hsym, hfun, hty, hresok, hrun⟩ := hok hk
  rw [hsig] at hsig'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hsig')
  obtain ⟨vtop, vr, hvs, hlen, hrest, hargs⟩ := stack_args ps hinv.stack
  have htake : sl.values.take ps.length = vtop := by rw [hvs, ← hlen]; simp
  have hdrop : sl.values.drop ps.length = vr := by rw [hvs, ← hlen]; simp
  have htyped : ArgsTyped ps sl.values := by
    refine ⟨by rw [hvs]; simp [hlen], ?_⟩
    rw [htake]
    exact hargs.allHas
  have hargv : argVals ps sl.values = vtop.reverse.map cval := by
    simp [argVals, htake]
  have hcallee : eval_expr A E.ge empty_env le m (.Evar (funId k) (funType ps rs)) (.Vptr b Ptrofs.zero) :=
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global hsym) (.deref_loc_reference rfl)
  have hfind : Genv.find_funct E.ge (.Vptr b Ptrofs.zero) = some (.Internal fd) := by
    simp [Genv.find_funct, hfun]
  have hevl : eval_exprlist A E.ge empty_env le m (callArgs σr.length ps) (ps.map VT.ty)
      (argVals ps sl.values) := by
    rw [hargv]; exact hargs.eval
  have hrun' := hrun st sl.values m env htyped hinv.store hinv.status
  simp only [execOne.eq_def]
  cases hres : run f mod k st sl.values env with
  | Success vs st' =>
      rw [hres] at hrun'
      obtain ⟨t, m', vres, hcall, hg, hs, hrel⟩ := hrun'
      have hscall : ∀ optid, exec_stmt A X E.ge empty_env le m
          (.Scall optid (.Evar (funId k) (funType ps rs)) (callArgs σr.length ps)) t
          (set_opttemp optid vres le) m' .Out_normal := fun optid =>
        .exec_Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl hcallee hevl hfind hty hcall
      have hchk := exec_statusCheck (A := A) (X := X) (le := le) (E := E) hE hs (by decide) c.result
      rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨t0, rfl, rfl, rfl, rfl⟩ | ⟨h2, rfl, rfl, rfl⟩
      · obtain ⟨rfl, -⟩ := hrel
        rw [hdrop]
        refine ⟨σr, rfl, hb, t ++ E0, le, m', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (hscall none)
          (by simpa [set_opttemp] using hchk), ?_, Frame.refl _ _⟩
        exact { stack := hrest, locals := hinv.locals, store := hg, status := hs,
                brk := hinv.brk }
      · obtain ⟨v, rfl, ht, rfl⟩ := hrel
        rw [hdrop]
        let le1 := le.insert (callId n) (cval v)
        let le2 := le1.insert (slotId σr.length t0) (cval v)
        have hset : exec_stmt A X E.ge empty_env le1 m' (.Sset (slotId σr.length t0)
            (.Etempvar (callId n) t0.ty)) E0 le2 m' .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _))
        have hchk2 := exec_statusCheck (A := A) (X := X) (le := le2) (E := E) hE hs (by decide)
          c.result
        have hframe : Frame σr.length le le2 := fun x hx t' => by
          rw [te_insert_ne _ (slotId_ne_of_height _ _ (by omega)),
            te_insert_ne _ (callId_ne_slotId _ _ _)]
        refine ⟨t0 :: σr, rfl, by simp; omega, (t ++ E0) ++ E0, le2, m',
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
            (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (hscall (some (callId n))) hset)
            (by simpa using hchk2), ?_, hframe.mono hb⟩
        refine { stack := ⟨ht, te_insert_same _ _ _, hrest.frame hframe⟩, locals := ?_,
                 store := hg, status := hs, brk := ?_ }
        · exact (hinv.locals.insert_other _ (fun i => callId_ne_localId _ i)).insert_other _
            (fun i => slotId_ne_localId _ _ i)
        · rw [te_insert_ne _ (slotId_ne_brkId _ _), te_insert_ne _ (callId_ne_brkId _)]
          exact hinv.brk
      · have hmany : ∃ ws, vs = ws ++ vr ∧ ws.length = rs.length ∧ vres = .Vundef ∧
            ResultsIn E rs ws m' := by
          rw [← hdrop]
          rcases rs with _ | ⟨t1, _ | ⟨t2, rs⟩⟩
          · simp at h2
          · simp at h2
          · exact hrel
        obtain ⟨ws, rfl, hwlen, rfl, hin⟩ := hmany
        obtain ⟨hnres, hint⟩ := hresok h2
        have hload : ∀ j (hj : j < rs.length), ∃ v, ws.reverse[j]? = some v ∧ rs[j].has v = true ∧
            Mem.load rs[j].chunk m' (E.res (0 + j) rs[j]) 0 = some (cval v) := by
          intro j hj
          obtain ⟨v, hv, htv, hl⟩ := hin.2 j hj
          rw [List.take_of_length_le (by omega)] at hv
          exact ⟨v, hv, htv, by simpa using hl⟩
        obtain ⟨le', hx, hargs', hother⟩ := exec_resLoads (A := A) (X := X) hE (m := m') rs 0
          σr.length ws.reverse le (by intro e; rw [e] at h2; simp at h2) (by omega) hint
          (by simp [hwlen]) hload
        have hframe : Frame σr.length le le' := fun x hx t' =>
          hother _ (fun j _ t'' => slotId_ne_of_height _ _ (by omega))
        have hchk2 := exec_statusCheck (A := A) (X := X) (le := le') (E := E) hE hs (by decide)
          c.result
        refine ⟨rs.reverse ++ σr, rfl, by simp; omega, (t ++ E0) ++ E0, le', m',
          .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
            (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (hscall none) hx)
            (by simpa using hchk2), ?_, hframe.mono hb⟩
        have hstack := stack_of_args rs hargs' (hrest.frame hframe)
        rw [List.reverse_reverse] at hstack
        refine { stack := hstack, locals := ?_, store := hg, status := hs, brk := ?_ }
        · refine ⟨hinv.locals.1, fun i hi => ?_⟩
          obtain ⟨w, hw, htw, hlw⟩ := hinv.locals.2 i hi
          exact ⟨w, hw, htw, by
            rw [hother _ (fun j _ t'' => (slotId_ne_localId _ _ i).symm)]; exact hlw⟩
        · rw [hother _ (fun j _ t'' => (slotId_ne_brkId _ _).symm)]
          exact hinv.brk
  | Trap st' msg =>
      rw [hres] at hrun'
      obtain ⟨t, m', vres, hcall, hg, hs, hc⟩ := hrun'
      have hscall : ∀ optid, exec_stmt A X E.ge empty_env le m
          (.Scall optid (.Evar (funId k) (funType ps rs)) (callArgs σr.length ps)) t
          (set_opttemp optid vres le) m' .Out_normal := fun optid =>
        .exec_Scall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ rfl hcallee hevl hfind hty hcall
      have hcode := trapCode_le msg
      rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨t0, rfl, rfl, rfl, rfl⟩ | ⟨h2, rfl, rfl, rfl⟩
      · have hchk := exec_statusCheck (A := A) (X := X) (le := le) (E := E) hE hs hcode c.result
        refine ⟨t ++ E0, le, m', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (hscall none)
          (by simpa [hc, set_opttemp] using hchk), hg, hs, hc⟩
      · let le1 := le.insert (callId n) vres
        let le2 := le1.insert (slotId σr.length t0) vres
        have hset : exec_stmt A X E.ge empty_env le1 m' (.Sset (slotId σr.length t0)
            (.Etempvar (callId n) t0.ty)) E0 le2 m' .Out_normal :=
          .exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ (te_insert_same _ _ _))
        have hchk := exec_statusCheck (A := A) (X := X) (le := le2) (E := E) hE hs hcode c.result
        exact ⟨(t ++ E0) ++ E0, le2, m', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
          (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (hscall (some (callId n))) hset)
          (by simpa [hc] using hchk), hg, hs, hc⟩
      · obtain ⟨hnres, hint⟩ := hresok h2
        obtain ⟨le', hx⟩ := exec_resLoads_any (A := A) (X := X) hE hg.2.resW rs 0 σr.length
          le (by intro e; rw [e] at h2; simp at h2) (by omega) hint
        have hchk := exec_statusCheck (A := A) (X := X) (le := le') (E := E) hE hs hcode c.result
        exact ⟨(t ++ E0) ++ E0, le', m', .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _
          (.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (hscall none) hx)
          (by simpa [hc] using hchk), hg, hs, hc⟩
  | Invalid _ => trivial
  | OutOfFuel => trivial
  | Thrown _ _ _ => rw [hres] at hrun'; exact hrun'.elim

end

end LeanExe.Native
