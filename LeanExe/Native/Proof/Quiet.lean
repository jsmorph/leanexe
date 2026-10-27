import LeanExe.Native.Proof.Whole

/-!
Runs without events.  The trace of a program is its output, so the theorem about a bare-metal
program needs the calls of the translation's functions to emit nothing.  The simulation
theorems state their executions with some trace, and this file shows that the trace is `E0`.

`quietS Q s` holds of a statement without built-in calls whose calls name a function `Evar id`
of a function type with `Q id`.  `exec_quiet` and `funcall_quiet` show that, in a global
environment where every function under an identifier of `Q` is quiet, an internal function
with a quiet body or a built-in function, such statements and calls emit no event.  Events
arise only from `external_call`, and the built-in functions of `known_builtin_sem` emit none.

The translator's statements are quiet for `trCallable`, which accepts `__builtin_fsqrt` and the
identifiers of functions: `instr_quiet_of` and `prog_quiet` follow `trInstr` and `trProg`, by
induction on the size of the instructions, and `trFunction_quiet` covers a function's body.
`genvQuiet_whole` concludes that, in the whole program, every function under such an
identifier is quiet, given the numbering of identifiers that `wholeOk_of` assumes.
-/

namespace LeanExe.Native

open LClight

/-! ## Quiet statements -/

mutual
  /-- No built-in calls, and every call names a function `Evar id` with `Q id`. -/
  def quietS (Q : ident → Bool) : statement → Bool
    | .Sbuiltin .. => false
    | .Scall _ (.Evar id (.Tfunction ..)) _ => Q id
    | .Scall .. => false
    | .Ssequence s1 s2 => quietS Q s1 && quietS Q s2
    | .Sloop s1 s2 => quietS Q s1 && quietS Q s2
    | .Sifthenelse _ s1 s2 => quietS Q s1 && quietS Q s2
    | .Sswitch _ sl => quietLS Q sl
    | .Slabel _ s => quietS Q s
    | .Sskip | .Sassign .. | .Sset .. | .Sbreak | .Scontinue | .Sreturn _ | .Sgoto _ => true

  def quietLS (Q : ident → Bool) : labeled_statements → Bool
    | .LSnil => true
    | .LScons _ s sl => quietS Q s && quietLS Q sl
end

/-- A function whose calls emit no event: an internal function with a quiet body, or a built-in
function. -/
def QuietF (Q : ident → Bool) : fundef function → Prop
  | .Internal f => quietS Q f.fn_body = true
  | .External ef _ _ _ => ∃ name sg, ef = .EF_builtin name sg

/-- Every function under an identifier of `Q` is quiet. -/
def GenvQuiet (Q : ident → Bool) (ge : genv) : Prop :=
  ∀ id b fd, Q id = true → Genv.find_symbol ge id = some b → Genv.find_funct_ptr ge b = some fd →
    QuietF Q fd

/-! ## Quiet runs emit no event -/

section

variable {A : Archi} {X : ExtSem} {Q : ident → Bool} {ge : genv}

/-- The function that a call of `Evar id` of a function type finds is the one under `id`. -/
theorem callee_of_evar {e : env} (he : e = empty_env) {le : temp_env} {m : mem} {id : ident}
    {ty : type} (hty : access_mode ty = .By_reference) {vf : val}
    (h : eval_expr A ge e le m (.Evar id ty) vf) :
    ∃ b, Genv.find_symbol ge id = some b ∧ vf = .Vptr b Ptrofs.zero := by
  subst he
  cases h with
  | eval_Elvalue _ loc ofs bf v hl hd =>
      cases hl with
      | eval_Evar_local _ _ _ hl => simp [empty_env] at hl
      | eval_Evar_global _ _ _ _ hs =>
          cases hd with
          | deref_loc_value chunk _ hm _ =>
              simp only [typeof] at hm
              rw [hty] at hm
              cases hm
          | deref_loc_reference _ => exact ⟨loc, hs, rfl⟩

theorem external_quiet {ef : external_function} {vargs : List val} {m : mem} {t : trace}
    {vres : val} {m' : mem} (hq : ∃ name sg, ef = .EF_builtin name sg)
    (h : external_call A X ef ge vargs m t vres m') : t = E0 := by
  obtain ⟨name, sg, rfl⟩ := hq
  simp only [external_call] at h
  cases hb : lookup_builtin_function name sg with
  | none => rw [hb] at h; exact h.elim
  | some bf => rw [hb] at h; exact h.2.1

mutual
  theorem exec_quiet (hge : GenvQuiet Q ge) {e : env} (he : e = empty_env) {le : temp_env}
      {m : mem} {s : statement} {t : trace} {le' : temp_env} {m' : mem} {out : outcome}
      (h : exec_stmt A X ge e le m s t le' m' out) (hq : quietS Q s = true) : t = E0 := by
    match h with
    | .exec_Sskip .. | .exec_Sassign .. | .exec_Sset .. | .exec_Sreturn_none ..
    | .exec_Sreturn_some .. | .exec_Sbreak .. | .exec_Scontinue .. => rfl
    | .exec_Scall _ _ _ optid a al tyargs tyres cconv vf vargs f tr m2 vres hcl ha hal hf hty
        hcall =>
        match a, hq, ha with
        | .Evar id (.Tfunction targs tres cc), hq, ha =>
            obtain ⟨b, hs, rfl⟩ := callee_of_evar he rfl ha
            have hptr : Genv.find_funct_ptr ge b = some f := by simpa [Genv.find_funct] using hf
            exact funcall_quiet hge hcall (hge id b f (by simpa [quietS] using hq) hs hptr)
    | .exec_Sbuiltin .. => simp [quietS] at hq
    | .exec_Sseq_1 _ _ _ s1 s2 t1 le1 m1 t2 le2 m2 out h1 h2 =>
        have hq' : quietS Q s1 = true ∧ quietS Q s2 = true := by simpa [quietS] using hq
        rw [exec_quiet hge he h1 hq'.1, exec_quiet hge he h2 hq'.2]; rfl
    | .exec_Sseq_2 _ _ _ s1 s2 t1 le1 m1 out h1 _ =>
        have hq' : quietS Q s1 = true ∧ quietS Q s2 = true := by simpa [quietS] using hq
        exact exec_quiet hge he h1 hq'.1
    | .exec_Sifthenelse _ _ _ a s1 s2 v1 b tr le2 m2 out _ _ hs =>
        have hq' : quietS Q s1 = true ∧ quietS Q s2 = true := by simpa [quietS] using hq
        exact exec_quiet hge he hs (by cases b <;> simp [hq'.1, hq'.2])
    | .exec_Sloop_stop1 _ _ _ s1 s2 tr le2 m2 out' out h1 _ =>
        have hq' : quietS Q s1 = true ∧ quietS Q s2 = true := by simpa [quietS] using hq
        exact exec_quiet hge he h1 hq'.1
    | .exec_Sloop_stop2 _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 out2 out h1 _ h2 _ =>
        have hq' : quietS Q s1 = true ∧ quietS Q s2 = true := by simpa [quietS] using hq
        rw [exec_quiet hge he h1 hq'.1, exec_quiet hge he h2 hq'.2]; rfl
    | .exec_Sloop_loop _ _ _ s1 s2 t1 le1 m1 out1 t2 le2 m2 t3 le3 m3 out h1 _ h2 h3 =>
        have hq' : quietS Q s1 = true ∧ quietS Q s2 = true := by simpa [quietS] using hq
        rw [exec_quiet hge he h1 hq'.1, exec_quiet hge he h2 hq'.2, exec_quiet hge he h3 hq]
        rfl

  theorem funcall_quiet (hge : GenvQuiet Q ge) {m : mem} {fd : fundef function}
      {vargs : List val} {t : trace} {m' : mem} {vres : val}
      (h : eval_funcall A X ge m fd vargs t m' vres) (hq : QuietF Q fd) : t = E0 := by
    match h with
    | .eval_funcall_internal _ f _ tr e le1 le2 m1 m2 out _ m3 hentry hbody _ _ =>
        have he : e = empty_env := by cases hentry; rfl
        exact exec_quiet hge he hbody hq
    | .eval_funcall_external _ ef targs tres cconv _ tr _ _ hx => exact external_quiet hq hx
end

end

/-! ## The translation's code is quiet -/

/-- The identifiers that the translation's code calls: `__builtin_fsqrt` and the functions. -/
def trCallable (id : ident) : Bool := id == sqrtId || id % 4 == 3

theorem trCallable_funId (k : Nat) : trCallable (funId k) = true := by
  have : (4 * k + 3) % 4 = 3 := by omega
  simp [trCallable, funId, this]

theorem quietS_seq (Q : ident → Bool) (a b : statement) :
    quietS Q (seq a b) = (quietS Q a && quietS Q b) := by
  cases a <;> simp [seq, quietS]

theorem quietS_seqList (Q : ident → Bool) :
    ∀ l : List statement, quietS Q (seqList l) = l.all (quietS Q)
  | [] => rfl
  | [s] => by simp [seqList]
  | s :: t :: rest => by
      show quietS Q (.Ssequence s (seqList (t :: rest))) = _
      rw [quietS, quietS_seqList Q (t :: rest)]
      simp

theorem quietS_storeBytes (Q : ident → Bool) (cap : Nat) (t : ident) (v : expr) :
    ∀ k n, quietS Q (storeBytes cap t v k n) = true
  | _, 0 => rfl
  | k, n + 1 => by simp [storeBytes, quietS, quietS_storeBytes Q cap t v (k + 1) n]

theorem quietS_resStores (Q : ident → Bool) :
    ∀ rs i h, ∀ s ∈ resStores rs i h, quietS Q s = true
  | [], _, _ => by simp [resStores]
  | t :: rs, i, h => by
      intro s hs
      simp only [resStores, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · exact quietS_resStores Q rs (i + 1) (h + 1) s hs

theorem quietS_resLoads (Q : ident → Bool) :
    ∀ rs i h, ∀ s ∈ resLoads rs i h, quietS Q s = true
  | [], _, _ => by simp [resLoads]
  | t :: rs, i, h => by
      intro s hs
      simp only [resLoads, List.mem_cons] at hs
      rcases hs with rfl | hs
      · rfl
      · exact quietS_resLoads Q rs (i + 1) (h + 1) s hs

/-- Every statement that the option holds is quiet. -/
def OQ {α : Type} (Q : ident → Bool) (o : Option (statement × α)) : Prop :=
  ∀ x, o = some x → quietS Q x.1 = true

theorem OQ_none {α : Type} (Q : ident → Bool) : OQ (α := α) Q none := fun _ h => by cases h

theorem OQ_pure {α : Type} {Q : ident → Bool} {s : statement} (a : α) (h : quietS Q s = true) :
    OQ Q (pure (s, a) : Option (statement × α)) := by
  intro x hx
  cases hx
  exact h

theorem OQ_bind {α β : Type} {Q : ident → Bool} {o : Option β} {f : β → Option (statement × α)}
    (h : ∀ b, o = some b → OQ Q (f b)) : OQ Q (o >>= f) := by
  intro x hx
  cases ho : o with
  | none => rw [ho] at hx; cases hx
  | some b => rw [ho] at hx; exact h b ho x hx

theorem OQ_ite {α : Type} {Q : ident → Bool} {c : Prop} [Decidable c]
    {a b : Option (statement × α)} (ha : c → OQ Q a) (hb : ¬c → OQ Q b) :
    OQ Q (if c then a else b) := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact ha hc
  · simp only [hc, ↓reduceIte]; exact hb hc


theorem all_resStores (Q : ident → Bool) (rs : List VT) (i h : Nat) :
    (resStores rs i h).all (quietS Q) = true :=
  List.all_eq_true.mpr (quietS_resStores Q rs i h)

theorem all_resLoads (Q : ident → Bool) (rs : List VT) (i h : Nat) :
    (resLoads rs i h).all (quietS Q) = true :=
  List.all_eq_true.mpr (quietS_resLoads Q rs i h)

theorem quietS_retZero (Q : ident → Bool) (r : Option VT) : quietS Q (retZero r) = true := by
  cases r <;> rfl

theorem quietS_jump (Q : ident → Bool) (b : Bool) : quietS Q (jump b) = true := by
  cases b <;> rfl

theorem quietS_trapStmt (Q : ident → Bool) (code : Nat) (r : Option VT) :
    quietS Q (trapStmt code r) = true := by
  simp [trapStmt, quietS, quietS_retZero]

theorem quietS_statusCheck (Q : ident → Bool) (r : Option VT) :
    quietS Q (statusCheck r) = true := by
  simp [statusCheck, quietS, quietS_retZero]

theorem quietS_dispatch (Q : ident → Bool) (l : Label) : quietS Q (dispatch l) = true := by
  simp [dispatch, quietS, quietS_jump]

theorem quietS_wrapLoop (Q : ident → Bool) (s : statement) :
    quietS Q (wrapLoop s) = quietS Q s := by
  simp [wrapLoop, quietS, quietS_seq]

theorem quietS_f64ConstStmt (Q : ident → Bool) (h : Nat) (v : UInt64) :
    quietS Q (f64ConstStmt h v) = true := by
  unfold f64ConstStmt
  split
  · split <;> rfl
  · rfl

theorem quietS_canonStmt (Q : ident → Bool) (h : Nat) : quietS Q (canonStmt h) = true := rfl

theorem quietS_truncSatStmt (Q : ident → Bool) (h : Nat) : quietS Q (truncSatStmt h) = true :=
  rfl

theorem quietS_punStore (Q : ident → Bool) (w : expr) (h : Nat) :
    quietS Q (punStore w h) = true := rfl

theorem brStmt_quiet (Q : ident → Bool) {L : List Label} {σ : List VT} {n : Nat} {s : statement}
    (h : brStmt L σ n = some s) : quietS Q s = true := by
  cases hL : L[n]? with
  | none => simp [brStmt, hL] at h
  | some target =>
      simp [brStmt, hL] at h
      obtain ⟨-, h⟩ := h
      repeat' split at h
      all_goals (try simp at h)
      all_goals (subst h; simp [quietS_seq, quietS, quietS_jump])

theorem OQ_some {α : Type} {Q : ident → Bool} {s : statement} (a : α) (h : quietS Q s = true) :
    OQ Q (some (s, a)) := by
  intro x hx
  cases hx
  exact h

theorem OQ_obind {α β : Type} {Q : ident → Bool} {o : Option β} {f : β → Option (statement × α)}
    (h : ∀ b, o = some b → OQ Q (f b)) : OQ Q (o.bind f) := by
  intro x hx
  cases ho : o with
  | none => rw [ho] at hx; cases hx
  | some b => rw [ho] at hx; exact h b ho x hx

/-- The statements of an instruction are quiet. -/
def InstrQuiet (inst : Wasm.Instruction) : Prop :=
  ∀ c L σ n, OQ (α := Option (List VT) × Nat) trCallable (trInstr c L σ n inst)

/-- The statements of a program are quiet. -/
def ProgQuiet (p : Wasm.Program) : Prop :=
  ∀ c L σ σend n, OQ (α := Nat) trCallable (trProg c L σ σend n p)

theorem trCallable_sqrtId : trCallable sqrtId = true := rfl

macro "oq_close" : tactic => `(tactic| simp [quietS, quietS_seq, quietS_seqList,
  quietS_storeBytes, quietS_trapStmt, quietS_statusCheck, quietS_dispatch, quietS_wrapLoop,
  quietS_f64ConstStmt, quietS_canonStmt, quietS_truncSatStmt, quietS_punStore, quietS_retZero,
  quietS_jump, all_resStores, all_resLoads, addrStmt, boundsCheck, trCallable_funId,
  trCallable_sqrtId, funType, sqrtVar])

macro "oq_step" : tactic => `(tactic| first
  | contradiction
  | exact OQ_none _
  | (apply OQ_some; oq_close; done)
  | (apply OQ_pure; oq_close; done)
  | (apply OQ_pure; have hq := brStmt_quiet trCallable ‹brStmt _ _ _ = some _›;
      simp [hq, quietS]; done)
  | (apply OQ_obind; intro _ _)
  | (apply OQ_bind; intro _ _)
  | (apply OQ_ite <;> intro _)
  | split)

theorem instr_quiet_of (inst : Wasm.Instruction)
    (H : ∀ p : Wasm.Program, sizeOf p < sizeOf inst → ProgQuiet p) : InstrQuiet inst := by
  intro c L σ n
  cases inst
  case block pa ra body pts rts =>
    have hb := H body (by simp; omega)
    unfold trInstr
    repeat' (first
      | (apply OQ_pure; have hq := hb _ _ _ _ _ _ ‹trProg _ _ _ _ _ body = some _›;
          simp_all [quietS, quietS_wrapLoop, quietS_dispatch])
      | oq_step)
  case loop pa ra body pts rts =>
    have hb := H body (by simp; omega)
    unfold trInstr
    repeat' (first
      | (apply OQ_pure; have hq := hb _ _ _ _ _ _ ‹trProg _ _ _ _ _ body = some _›;
          simp_all [quietS, quietS_wrapLoop, quietS_dispatch])
      | oq_step)
  case iff pa ra thn els pts rts =>
    have hb1 := H thn (by simp; omega)
    have hb2 := H els (by simp; omega)
    unfold trInstr
    repeat' (first
      | (apply OQ_pure; have hq1 := hb1 _ _ _ _ _ _ ‹trProg _ _ _ _ _ thn = some _›;
          have hq2 := hb2 _ _ _ _ _ _ ‹trProg _ _ _ _ _ els = some _›;
          simp_all [quietS, quietS_wrapLoop, quietS_dispatch])
      | oq_step)
  all_goals unfold trInstr
  all_goals repeat' oq_step

theorem prog_quiet_lt : ∀ (N : Nat) (p : Wasm.Program), sizeOf p < N → ProgQuiet p
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | N + 1, p, h => by
      intro c L σ σend n
      cases p with
      | nil =>
          unfold trProg
          split
          · exact OQ_some _ rfl
          · exact OQ_none _
      | cons inst rest =>
          have hs : sizeOf (inst :: rest) = 1 + sizeOf inst + sizeOf rest := rfl
          have hi : InstrQuiet inst :=
            instr_quiet_of inst fun q hq => prog_quiet_lt N q (by omega)
          have hr : ProgQuiet rest := prog_quiet_lt N rest (by omega)
          unfold trProg
          apply OQ_bind
          rintro ⟨s, σ', n'⟩ hx
          have hq : quietS trCallable s = true := hi c L σ n _ hx
          cases rest with
          | nil =>
              cases σ' with
              | none => exact OQ_pure _ hq
              | some σ'' =>
                  dsimp only
                  split
                  · exact OQ_pure _ hq
                  · exact OQ_none _
          | cons i2 rest2 =>
              cases σ' with
              | none => exact OQ_none _
              | some σ'' =>
                  dsimp only
                  apply OQ_bind
                  rintro ⟨s2, n''⟩ hx2
                  exact OQ_pure _ (by simp [quietS, hq, hr _ _ _ _ _ _ hx2])

theorem prog_quiet (p : Wasm.Program) : ProgQuiet p := prog_quiet_lt _ p (Nat.lt_succ_self _)

theorem quietS_retStmt (Q : ident → Bool) (rs : List VT) : quietS Q (retStmt rs) = true := by
  unfold retStmt
  split
  · rfl
  · rfl
  · simp [quietS_seqList, all_resStores, quietS]

/-- The body of a translated function is quiet. -/
theorem trFunction_quiet {cap : Nat} {sigs : List (Option (List VT × List VT))} {G : Nat}
    {f : Wasm.Function} {fd : function} (h : trFunction cap sigs G f = some fd) :
    quietS trCallable fd.fn_body = true := by
  simp [trFunction, Option.bind_eq_some_iff] at h
  obtain ⟨ps, -, ls, -, rs, -, -, body, ⟨n', hb⟩, rfl⟩ := h
  have hq := prog_quiet _ _ _ _ _ _ _ hb
  simp only at hq
  simp [quietS_seqList, quietS, quietS_wrapLoop, hq, quietS_retStmt]


/-! ## The whole program's functions are quiet -/

theorem def_unique {α : Type} : ∀ {l : List (ident × α)}, (l.map (·.1)).Nodup →
    ∀ {id : ident} {d1 d2 : α}, (id, d1) ∈ l → (id, d2) ∈ l → d1 = d2
  | [], _, _, _, _, h1, _ => by simp at h1
  | x :: l, hn, id, d1, d2, h1, h2 => by
      rw [List.map_cons, List.nodup_cons] at hn
      rcases List.mem_cons.mp h1 with e1 | h1 <;> rcases List.mem_cons.mp h2 with e2 | h2
      · rw [← e1] at e2; cases e2; rfl
      · exact (hn.1 (by rw [← e1]; exact List.mem_map_of_mem (f := (·.1)) h2)).elim
      · exact (hn.1 (by rw [← e2]; exact List.mem_map_of_mem (f := (·.1)) h1)).elim
      · exact def_unique hn.2 h1 h2

/-- The definition under the symbol `id` of the global environment of a program with distinct
identifiers is the program's definition of `id`. -/
theorem mem_of_find {p : program function} (hn : (p.prog_defs.map (·.1)).Nodup) {id : ident}
    {b : block} {d : globdef (fundef function) type}
    (hs : Genv.find_symbol (globalenv p) id = some b) (hd : Genv.find_def (globalenv p) b = some d) :
    (id, d) ∈ p.prog_defs := by
  by_cases hid : id ∈ p.prog_defs.map (·.1)
  · obtain ⟨⟨id', d'⟩, hmem, rfl⟩ := List.mem_map.mp hid
    obtain ⟨b', hs', hd'⟩ := Genv.find_add_globals (Genv.empty_genv p.prog_public) p.prog_defs hn hmem
    have hb : b = b' := Option.some.inj (hs.symm.trans hs')
    subst hb
    have hdd : d = d' := Option.some.inj (hd.symm.trans hd')
    subst hdd
    exact hmem
  · have := (Genv.add_globals_keep (Genv.empty_genv p.prog_public) p.prog_defs).1 id hid
    rw [show globalenv p = Genv.add_globals (Genv.empty_genv p.prog_public) p.prog_defs from rfl,
      this] at hs
    simp [Genv.find_symbol, Genv.empty_genv] at hs

/-- A function of a translation under an identifier that leaves the remainder 3 modulo 4 is a
translated function, whose body is quiet. -/
theorem translation_fun_quiet {m : Wasm.Module} {cap : Nat} {T : Translation}
    (h : translate cap m = some T) {id : ident} {fd : fundef function}
    (hd : (id, globdef.Gfun fd) ∈ T.cprogram.prog_defs) (hid : id % 4 = 3) : QuietF trCallable fd := by
  obtain ⟨-, -, hspec⟩ := translate_spec h
  obtain ⟨decl, gdefs, funs, -, -, -, -, -, hfuns, hdefs⟩ := translate_defs h
  have hd0 := hd
  rw [hdefs] at hd
  simp only [progDefs, List.mem_cons, List.mem_append, List.mem_map, Prod.mk.injEq,
    reduceCtorEq, and_false, false_or,] at hd
  have hid' : @HMod.hMod Nat Nat Nat instHMod id 4 = 3 := hid
  rcases hd with ⟨-, h0⟩ | ⟨rfl, -⟩ | hd | hd | ⟨rfl, -⟩ | hd
  · exact h0.elim
  · exact absurd hid (by decide)
  · have hx : id ∈ resIds T.nres := by
      rw [← resDefs_ids]
      exact List.mem_map_of_mem (f := fun d : ident × globdef (fundef function) type => d.1) hd
    have := (mem_resIds hx).1
    omega
  · obtain ⟨fd', hfd'⟩ := (funDef_ids hfuns).2 _ hd
    simp only at hfd'
    cases hfd'
    have hx := List.mem_map_of_mem (f := (·.1)) hd
    rw [(funDef_ids hfuns).1] at hx
    obtain ⟨k, -, hk⟩ := List.mem_map.mp hx
    simp only at hk
    subst hk
    obtain ⟨f, -, -, htr, -⟩ := hspec k fd' hd0
    exact trFunction_quiet htr
  · exact absurd hid (by decide)
  · simp at hd

/-- Under the conditions of `wholeOk_of` on identifiers, every function of the whole program
under an identifier of `trCallable` is quiet. -/
theorem genvQuiet_whole {m : Wasm.Module} {cap : Nat} {T : Translation} (h : translate cap m = some T)
    {pre post : List (ident × globdef (fundef function) type)} (hw : WholeOk pre post T)
    (hids : ∀ x : Nat, x ∈ pre.map (·.1) → x = 24 ∨ (x % 4 = 1 ∧ x ≠ 1))
    (hidp : ∀ x : Nat, x ∈ post.map (·.1) → x = 4 ∨ x = 28) :
    GenvQuiet trCallable (globalenv (wholeProgram pre post T)) := by
  intro id b fd hq hs hf
  have hd : Genv.find_def (globalenv (wholeProgram pre post T)) b = some (.Gfun fd) := by
    simp only [Genv.find_funct_ptr] at hf
    split at hf
    · cases hf; assumption
    · cases hf
  have hmem := mem_of_find hw.nodup hs hd
  simp only [trCallable, Bool.or_eq_true, beq_iff_eq] at hq
  rcases hq with rfl | hq
  · have := def_unique hw.nodup hmem (by
      simp only [wholeDefs, List.mem_append]; exact .inl (.inl hw.sqrt))
    cases this
    exact ⟨_, _, rfl⟩
  · have hq' : @HMod.hMod Nat Nat Nat instHMod id 4 = 3 := by simpa using hq
    simp only [wholeProgram, wholeDefs, List.mem_append, List.mem_filter] at hmem
    rcases hmem with (hmem | ⟨hmem, -⟩) | hmem
    · have := hids id (List.mem_map_of_mem (f := (·.1)) hmem)
      omega
    · exact translation_fun_quiet h hmem hq'
    · have := hidp id (List.mem_map_of_mem (f := (·.1)) hmem)
      omega

end LeanExe.Native
