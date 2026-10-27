import LeanExe.Native.Proof.Relation

/-!
The simulation of the instructions that do not branch or call: locals, globals, constants, the
integer operations, and `unreachable`.  Each lemma states `InstrSim` for one instruction: from a
C state related to a Talos state, the instruction's C statement does what Talos's `execOne`
does, as `Outcome` relates them.
-/

namespace LeanExe.Native

open Wasm LClight

/-! ## Talos locals -/

theorem locals_get (s : Locals) (i : Nat) : s.get i = (s.params ++ s.locals)[i]? := by
  unfold Locals.get
  split
  · rw [List.getElem?_append_left (by assumption)]
  · split
    · rw [List.getElem?_append_right (by omega)]
    · rw [List.getElem?_eq_none (by simp; omega)]

theorem locals_set (s : Locals) (i : Nat) (v : Value) (hi : i < (s.params ++ s.locals).length) :
    ∃ s', s.set? i v = some s' ∧ s'.params ++ s'.locals = (s.params ++ s.locals).set i v ∧
      s'.values = s.values := by
  unfold Locals.set?
  split
  · exact ⟨_, rfl, by rw [List.set_append_left _ _ (by assumption)], rfl⟩
  · split
    · exact ⟨_, rfl, by rw [List.set_append_right _ _ (by omega)], rfl⟩
    · simp at hi; omega

theorem LocalsRel.get {le : temp_env} {tys : List VT} {vals : List Value} (h : LocalsRel le tys vals)
    {i : Nat} {t : VT} (ht : tys[i]? = some t) :
    ∃ v, vals[i]? = some v ∧ t.has v = true ∧ le[localId i]? = some (cval v) := by
  have hi : i < tys.length := (List.getElem?_eq_some_iff.mp ht).1
  have e : tys[i] = t := (List.getElem?_eq_some_iff.mp ht).2
  obtain ⟨v, hv, htv, hl⟩ := h.2 i hi
  exact ⟨v, hv, e ▸ htv, hl⟩

theorem LocalsRel.set {le : temp_env} {tys : List VT} {vals : List Value} (h : LocalsRel le tys vals)
    {i : Nat} {t : VT} (ht : tys[i]? = some t) {v : Value} (hv : t.has v = true) :
    LocalsRel (le.insert (localId i) (cval v)) tys (vals.set i v) := by
  have hi : i < tys.length := (List.getElem?_eq_some_iff.mp ht).1
  have e : tys[i] = t := (List.getElem?_eq_some_iff.mp ht).2
  refine ⟨by rw [List.length_set]; exact h.1, fun j hj => ?_⟩
  by_cases hij : i = j
  · subst hij
    refine ⟨v, ?_, e ▸ hv, te_insert_same _ _ _⟩
    rw [List.getElem?_set_self (by rw [h.1]; exact hi)]
  · obtain ⟨w, hw, htw, hl⟩ := h.2 j hj
    refine ⟨w, ?_, htw, ?_⟩
    · rw [List.getElem?_set_ne hij]; exact hw
    · rw [te_insert_ne _ (fun e => hij (localId_inj e))]; exact hl

/-! ## Values on the stack -/

theorem has_i64 {v : Value} (h : VT.has .i64 v = true) : ∃ x, v = .i64 x := by
  cases v <;> simp_all [VT.has]

theorem has_i32 {v : Value} (h : VT.has .i32 v = true) : ∃ x, v = .i32 x := by
  cases v <;> simp_all [VT.has]

theorem StackRel.cons_inv {le : temp_env} {t : VT} {σ : List VT} {vs : List Value}
    (h : StackRel le (t :: σ) vs) :
    ∃ v vr, vs = v :: vr ∧ t.has v = true ∧ le[slotId σ.length t]? = some (cval v) ∧
      StackRel le σ vr := by
  cases vs with
  | nil => simp [StackRel] at h
  | cons v vr => exact ⟨v, vr, rfl, h.1, h.2.1, h.2.2⟩

/-! ## Environments and globals -/

/-- The blocks of `E` are those of `lx_status` and the C globals in `E.ge`, all distinct. -/
structure EnvOk (E : Env) : Prop where
  status : Genv.find_symbol E.ge statusId = some E.status
  globals : ∀ i (h : i < E.globals.length), Genv.find_symbol E.ge (globalId i) = some E.globals[i]
  nodup : E.globals.Nodup
  status_not : E.status ∉ E.globals

theorem empty_env_none (id : ident) : empty_env[id]? = none := Std.TreeMap.getElem?_emptyc

theorem eval_lvalue_global {A : Archi} {ge : genv} {le : temp_env} {m : mem} {id : ident}
    {b : block} {ty : type} (h : Genv.find_symbol ge id = some b) :
    eval_lvalue A ge empty_env le m (.Evar id ty) b Ptrofs.zero .Full :=
  .eval_Evar_global id b ty (empty_env_none id) h

theorem ptrofs_unsigned_zero : Ptrofs.unsigned Ptrofs.zero = 0 := rfl

theorem loadv_zero (chunk : memory_chunk) (m : mem) (b : block) (h : size_chunk chunk ≤ 8) :
    Mem.loadv chunk m (.Vptr b Ptrofs.zero) = Mem.load chunk m b 0 := by
  simp only [Mem.loadv]
  split
  · rfl
  · rename_i hc
    exact absurd (by rw [ptrofs_unsigned_zero]; simp only [Ptrofs.modulus]; omega) hc

theorem storev_zero (chunk : memory_chunk) (m : mem) (b : block) (v : val)
    (h : size_chunk chunk ≤ 8) :
    Mem.storev chunk m (.Vptr b Ptrofs.zero) v = Mem.store chunk m b 0 v := by
  simp only [Mem.storev]
  split
  · rfl
  · rename_i hc
    exact absurd (by rw [ptrofs_unsigned_zero]; simp only [Ptrofs.modulus]; omega) hc

theorem eval_global_long {A : Archi} {ge : genv} {le : temp_env} {m : mem} {id : ident}
    {b : block} {n : UInt64} (h : Genv.find_symbol ge id = some b)
    (hl : Mem.load .Mint64 m b 0 = some (.Vlong n)) :
    eval_expr A ge empty_env le m (.Evar id tulong) (.Vlong n) :=
  .eval_Elvalue _ _ _ _ _ (eval_lvalue_global h)
    (.deref_loc_value .Mint64 _ rfl (by rw [loadv_zero _ _ _ (by decide)]; exact hl))

theorem eval_global_int {A : Archi} {ge : genv} {le : temp_env} {m : mem} {id : ident}
    {b : block} {n : UInt32} (h : Genv.find_symbol ge id = some b)
    (hl : Mem.load .Mint32 m b 0 = some (.Vint n)) :
    eval_expr A ge empty_env le m (.Evar id tuint) (.Vint n) :=
  .eval_Elvalue _ _ _ _ _ (eval_lvalue_global h)
    (.deref_loc_value .Mint32 _ rfl (by rw [loadv_zero _ _ _ (by decide)]; exact hl))

theorem exec_assign_long {A : Archi} {X : ExtSem} {ge : genv} {le : temp_env} {m : mem}
    {id : ident} {b : block} {e : expr} {n : UInt64} (h : Genv.find_symbol ge id = some b)
    (he : eval_expr A ge empty_env le m e (.Vlong n)) (ht : typeof e = tulong)
    (hva : Mem.valid_access m .Mint64 b 0 .Writable) :
    exec_stmt A X ge empty_env le m (.Sassign (.Evar id tulong) e) E0 le
      (Mem.stored .Mint64 m b 0 (.Vlong n)) .Out_normal :=
  .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ (eval_lvalue_global h) he (by rw [ht]; rfl)
    (.assign_loc_value _ .Mint64 _ rfl
      (by rw [storev_zero _ _ _ _ (by decide)]; exact Mem.store_ok _ hva))

theorem exec_assign_int {A : Archi} {X : ExtSem} {ge : genv} {le : temp_env} {m : mem}
    {id : ident} {b : block} {e : expr} {n : UInt32} (h : Genv.find_symbol ge id = some b)
    (he : eval_expr A ge empty_env le m e (.Vint n)) (ht : typeof e = tuint)
    (hva : Mem.valid_access m .Mint32 b 0 .Writable) :
    exec_stmt A X ge empty_env le m (.Sassign (.Evar id tuint) e) E0 le
      (Mem.stored .Mint32 m b 0 (.Vint n)) .Out_normal :=
  .exec_Sassign _ _ _ _ _ _ _ _ _ _ _ (eval_lvalue_global h) he (by rw [ht]; rfl)
    (.assign_loc_value _ .Mint32 _ rfl
      (by rw [storev_zero _ _ _ _ (by decide)]; exact Mem.store_ok _ hva))

theorem GlobalsRel.store_status {E : Env} {gs : List Value} {m : mem} (hE : EnvOk E)
    (h : GlobalsRel E gs m) (v : val) :
    GlobalsRel E gs (Mem.stored .Mint32 m E.status 0 v) := by
  refine ⟨h.1, fun i hi => ?_⟩
  obtain ⟨n, hn, hl, hv⟩ := h.2 i hi
  have hne : E.status ≠ E.globals[i] := fun e => hE.status_not (e ▸ List.getElem_mem hi)
  exact ⟨n, hn, by rw [Mem.load_stored_other _ _ _ _ _ _ _ _ hne]; exact hl, hv⟩

theorem StatusRel.store_status {E : Env} {m : mem} {k : Nat} (h : StatusRel E m k) (code : Nat) :
    StatusRel E (Mem.stored .Mint32 m E.status 0 (.Vint (UInt32.ofNat code))) code :=
  ⟨Mem.load_stored_int _ _ _ _ h.2, h.2⟩

theorem GlobalsRel.store_global {E : Env} {gs : List Value} {m : mem} (hE : EnvOk E)
    (h : GlobalsRel E gs m) {i : Nat} (hi : i < E.globals.length) (n : UInt64) :
    GlobalsRel E (gs.set i (.i64 n)) (Mem.stored .Mint64 m E.globals[i] 0 (.Vlong n)) := by
  refine ⟨by rw [List.length_set]; exact h.1, fun j hj => ?_⟩
  obtain ⟨w, hw, hl, hv⟩ := h.2 j hj
  by_cases hij : i = j
  · subst hij
    exact ⟨n, by rw [List.getElem?_set_self (by rw [h.1]; exact hi)],
      Mem.load_stored_long _ _ _ _ hv, hv⟩
  · have hne : E.globals[i] ≠ E.globals[j] := fun e =>
      hij (hE.nodup.getElem_inj.mp e)
    exact ⟨w, by rw [List.getElem?_set_ne hij]; exact hw,
      by rw [Mem.load_stored_other _ _ _ _ _ _ _ _ hne]; exact hl, hv⟩

theorem StatusRel.store_global {E : Env} {m : mem} {k : Nat} (hE : EnvOk E) (h : StatusRel E m k)
    {i : Nat} (hi : i < E.globals.length) (v : val) :
    StatusRel E (Mem.stored .Mint64 m E.globals[i] 0 v) k := by
  have hne : E.globals[i] ≠ E.status := fun e => hE.status_not (e ▸ List.getElem_mem hi)
  exact ⟨by rw [Mem.load_stored_other _ _ _ _ _ _ _ _ hne]; exact h.1, h.2⟩

/-! ## Traps -/

theorem typeof_zero (t : VT) : typeof t.zero = t.ty := by cases t <;> rfl

theorem exec_retZero (A : Archi) (X : ExtSem) (ge : genv) (le : temp_env) (m : mem)
    (r : Option VT) : exec_stmt A X ge empty_env le m (retZero r) E0 le m (trapOut r) := by
  cases r with
  | none => exact .exec_Sreturn_none _ _ _
  | some t =>
      have := exec_stmt.exec_Sreturn_some (A := A) (X := X) (ge := ge) empty_env le m t.zero (zval t)
        (eval_zero A ge empty_env le m t)
      rw [typeof_zero] at this
      exact this

theorem trap_exec {A : Archi} {X : ExtSem} {E : Env} (hE : EnvOk E) {le : temp_env} {m : mem}
    {gs : List Value} (hg : GlobalsRel E gs m) (hs : StatusRel E m 0) (code : Nat)
    (r : Option VT) :
    ∃ m', exec_stmt A X E.ge empty_env le m (trapStmt code r) E0 le m' (trapOut r) ∧
      GlobalsRel E gs m' ∧ StatusRel E m' code := by
  refine ⟨Mem.stored .Mint32 m E.status 0 (.Vint (UInt32.ofNat code)), ?_,
    hg.store_status hE _, hs.store_status code⟩
  have h1 := exec_assign_int (A := A) (X := X) (le := le) hE.status
    (.eval_Econst_int (UInt32.ofNat code) tuint) rfl hs.2
  have := exec_stmt.exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ h1 (exec_retZero A X E.ge le _ r)
  simpa [trapStmt, cint, E0] using this

/-! ## The claim for one instruction -/

section

variable (A : Archi) (X : ExtSem) (E : Env) (mod : Module) (c : FCtx)

/-- The simulation of `inst` at fuel `F`. -/
def InstrSim (F : Nat) (inst : Instruction) : Prop :=
  ∀ (L : List Label) (σ : List VT) (n : Nat) (s : statement) (σ' : Option (List VT)) (n' : Nat),
    trInstr c L σ n inst = some (s, σ', n') → curBase L ≤ σ.length →
    ∀ {α : Type} (st : Store α) (sl : Locals) (le : temp_env) (m : mem) (env : HostEnv α),
      Inv E c σ st sl le m → Outcome A X E c L σ' (execOne F mod st sl inst env) s le m

variable {A X E c}

/-- An instruction that replaces the values above `σr` by `v` of type `t`, by setting the slot at
height `σr.length` to `e`. -/
theorem push_step {L : List Label} {σr : List VT} {α : Type} {st : Store α} {sl : Locals}
    {le : temp_env} {m : mem} {e : expr} {v : Value} {t : VT} {vr : List Value}
    (hrest : StackRel le σr vr) (hloc : LocalsRel le c.locals (sl.params ++ sl.locals))
    (hg : GlobalsRel E st.globals.globals m) (hs : StatusRel E m 0)
    (hb : le[brkId]? = some (.Vint 0))
    (he : eval_expr A E.ge empty_env le m e (cval v)) (ht : t.has v = true)
    (hbase : curBase L ≤ σr.length) :
    Outcome A X E c L (some (t :: σr))
      (.Fallthrough st { params := sl.params, locals := sl.locals, values := v :: vr })
      (.Sset (slotId σr.length t) e) le m := by
  refine ⟨t :: σr, rfl, by simp; omega, E0, le.insert (slotId σr.length t) (cval v), m,
    .exec_Sset _ _ _ _ _ _ he, ?_, Frame.insert_slot _ _ _ _ hbase⟩
  exact { stack := ⟨ht, te_insert_same _ _ _, hrest.frame (Frame.insert_slot _ _ _ _ (Nat.le_refl _))⟩
          locals := hloc.insert_other _ (fun i => slotId_ne_localId _ _ i)
          globals := hg
          status := hs
          brk := by rw [te_insert_ne _ (slotId_ne_brkId _ _)]; exact hb }

theorem sim_zero_fuel {L : List Label} {σ' : Option (List VT)} {s : statement} {le : temp_env}
    {m : mem} {α : Type} {st : Store α} {sl : Locals} {env : HostEnv α} {inst : Instruction}
    (h : execOne 0 mod st sl inst env = .OutOfFuel) :
    Outcome A X E c L σ' (execOne 0 mod st sl inst env) s le m := by
  rw [h]; trivial

theorem sim_localGet (F i : Nat) : InstrSim A X E mod c F (.localGet i) := by
  intro L σ n s σ' n' htr hbase α st sl le m env hinv
  simp [trInstr, Option.bind_eq_some_iff] at htr
  obtain ⟨t, ht, rfl, rfl, rfl⟩ := htr
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      obtain ⟨v, hv, htv, hl⟩ := hinv.locals.get ht
      simp only [execOne.eq_def, locals_get, hv]
      exact push_step hinv.stack hinv.locals hinv.globals hinv.status hinv.brk
        (.eval_Etempvar _ _ _ hl) htv hbase

theorem sim_localSet (F i : Nat) : InstrSim A X E mod c F (.localSet i) := by
  intro L σ n s σ' n' htr hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at htr
  obtain ⟨t, ht, _, ⟨hb, rfl⟩, rfl, rfl, rfl, rfl⟩ := htr
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      obtain ⟨v, vr, hvs, htv, hl, hrest⟩ := hinv.stack.cons_inv
      have hi : i < (sl.params ++ sl.locals).length := by
        rw [hinv.locals.1]; exact (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨s', hs', hpl, -⟩ := locals_set sl i v hi
      simp only [execOne.eq_def, hvs, hs']
      refine ⟨σr, rfl, hb, E0, le.insert (localId i) (cval v), m,
        .exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ hl), ?_, Frame.insert_other _ _ _
          (fun x t' => (slotId_ne_localId x t' i).symm)⟩
      exact { stack := hrest.insert_other _ (fun x t' => (slotId_ne_localId x t' i).symm)
              locals := by
                show LocalsRel _ _ (s'.params ++ s'.locals)
                rw [hpl]; exact hinv.locals.set ht htv
              globals := hinv.globals
              status := hinv.status
              brk := brk_insert_local i _ hinv.brk }

theorem sim_localTee (F i : Nat) : InstrSim A X E mod c F (.localTee i) := by
  intro L σ n s σ' n' htr hbase α st sl le m env hinv
  rcases σ with _ | ⟨a, σr⟩ <;> simp [trInstr, pops, Option.bind_eq_some_iff] at htr
  obtain ⟨t, ht, _, ⟨hb, rfl⟩, rfl, rfl, rfl, rfl⟩ := htr
  cases F with
  | zero => simp only [execOne.eq_def, Outcome]
  | succ f =>
      obtain ⟨v, vr, hvs, htv, hl, hrest⟩ := hinv.stack.cons_inv
      have hi : i < (sl.params ++ sl.locals).length := by
        rw [hinv.locals.1]; exact (List.getElem?_eq_some_iff.mp ht).1
      obtain ⟨s', hs', hpl, hvals⟩ := locals_set sl i v hi
      simp only [execOne.eq_def, hvs, hs']
      refine ⟨a :: σr, rfl, by simp; omega, E0, le.insert (localId i) (cval v), m,
        .exec_Sset _ _ _ _ _ _ (.eval_Etempvar _ _ _ hl), ?_, Frame.insert_other _ _ _
          (fun x t' => (slotId_ne_localId x t' i).symm)⟩
      exact { stack := by
                rw [hvals, hvs]
                exact ⟨htv, by rw [te_insert_ne _ (slotId_ne_localId _ _ i).symm]; exact hl,
                  hrest.insert_other _ (fun x t' => (slotId_ne_localId x t' i).symm)⟩
              locals := by rw [hpl]; exact hinv.locals.set ht htv
              globals := hinv.globals
              status := hinv.status
              brk := brk_insert_local i _ hinv.brk }

end

end LeanExe.Native
