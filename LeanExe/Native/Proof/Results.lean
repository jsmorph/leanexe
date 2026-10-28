import LeanExe.Native.Proof.MemOps

/-!
A function with several results stores them in the result globals before it returns, and its
caller copies them into its stack slots.  `exec_resStores` runs the stores of
`ret` and of a function's end, and `exec_resLoads` the copies after a call.  `ArgsRel` relates
the slots from a height up to a list of values, deepest first, and `stack_args` and
`stack_of_args` move between it and `StackRel`.
-/

namespace LeanExe.Native

open Wasm LClight

/-- Each value has the type at its position. -/
def AllHas : List VT → List Value → Prop
  | [], [] => True
  | t :: ts, v :: vs => t.has v = true ∧ AllHas ts vs
  | _, _ => False

/-- The slots from height `base` up hold `vals`, deepest first, of the types `ps`. -/
def ArgsRel (le : temp_env) : Nat → List VT → List Value → Prop
  | _, [], [] => True
  | base, t :: ts, v :: vs =>
      t.has v = true ∧ le[slotId base t]? = some (cval v) ∧ ArgsRel le (base + 1) ts vs
  | _, _, _ => False

theorem stack_args {le : temp_env} (ps : List VT) {σr : List VT} {vs : List Value}
    (h : StackRel le (ps.reverse ++ σr) vs) :
    ∃ vtop vr, vs = vtop ++ vr ∧ vtop.length = ps.length ∧ StackRel le σr vr ∧
      ArgsRel le σr.length ps vtop.reverse := by
  induction ps generalizing σr vs with
  | nil => exact ⟨[], vs, rfl, rfl, by simpa using h, trivial⟩
  | cons p ps ih =>
      have h' : StackRel le (ps.reverse ++ (p :: σr)) vs := by simpa using h
      obtain ⟨vtop, vr', rfl, hlen, hrest, hargs⟩ := ih h'
      obtain ⟨v, vr, rfl, ht, hl, hrest'⟩ := hrest.cons_inv
      refine ⟨vtop ++ [v], vr, by simp, by simp [hlen], hrest', ?_⟩
      simp only [List.reverse_append, List.reverse_singleton, List.singleton_append]
      exact ⟨ht, hl, by simpa using hargs⟩

theorem ArgsRel.length {le : temp_env} {base : Nat} {ps : List VT} {vs : List Value}
    (h : ArgsRel le base ps vs) : vs.length = ps.length := by
  induction ps generalizing base vs with
  | nil => cases vs <;> simp_all [ArgsRel]
  | cons p ps ih =>
      cases vs with
      | nil => simp [ArgsRel] at h
      | cons v vs => simp [ih h.2.2]

theorem ArgsRel.allHas {le : temp_env} {base : Nat} {ps : List VT} {vs : List Value}
    (h : ArgsRel le base ps vs) : AllHas ps vs := by
  induction ps generalizing base vs with
  | nil => cases vs <;> simp_all [ArgsRel, AllHas]
  | cons p ps ih =>
      cases vs with
      | nil => simp [ArgsRel] at h
      | cons v vs => exact ⟨h.1, ih h.2.2⟩

theorem stack_of_args {le : temp_env} (ts : List VT) {σr : List VT} {ws vr : List Value}
    (h : ArgsRel le σr.length ts ws) (hr : StackRel le σr vr) :
    StackRel le (ts.reverse ++ σr) (ws.reverse ++ vr) := by
  induction ts generalizing σr ws vr with
  | nil =>
      cases ws with
      | nil => simpa using hr
      | cons _ _ => simp [ArgsRel] at h
  | cons t ts ih =>
      cases ws with
      | nil => simp [ArgsRel] at h
      | cons w ws =>
          obtain ⟨ht, hl, hrest⟩ := h
          have h' := ih (σr := t :: σr) (ws := ws) (vr := w :: vr) (by simpa using hrest)
            ⟨ht, hl, hr⟩
          simpa using h'

theorem ArgsRel.frame {le le' : temp_env} {base : Nat} {ts : List VT} {ws : List Value}
    (h : ArgsRel le base ts ws)
    (hf : ∀ j < ts.length, ∀ t, le'[slotId (base + j) t]? = le[slotId (base + j) t]?) :
    ArgsRel le' base ts ws := by
  induction ts generalizing base ws with
  | nil => cases ws <;> simp_all [ArgsRel]
  | cons t ts ih =>
      cases ws with
      | nil => simp [ArgsRel] at h
      | cons w ws =>
          obtain ⟨ht, hl, hrest⟩ := h
          refine ⟨ht, by rw [show base = base + 0 from rfl, hf 0 (by simp) t]; exact hl,
            ih hrest fun j hj t' => ?_⟩
          rw [show base + 1 + j = base + (j + 1) by omega]
          exact hf (j + 1) (by simp; omega) t'

/-- Several results fit in the result globals of `E`. -/
def ResOk (E : Env) (rs : List VT) : Prop :=
  2 ≤ rs.length → rs.length ≤ E.nres ∧ rs.all VT.isRes = true

theorem VT.isRes_cases {t : VT} (_h : t.isRes = true) :
    t = .i32 ∨ t = .i64 ∨ t = .f64 ∨ t = .f32 := by
  cases t <;> simp

section

variable {A : Archi} {X : ExtSem} {E : Env}

theorem eval_res (hE : EnvOk E) {le : temp_env} {m : mem} {i : Nat} {t : VT} {v : Value}
    (hi : i < E.nres) (ht : t.isRes = true)
    (hl : Mem.load t.chunk m (E.res i t) 0 = some (cval v)) :
    eval_expr A E.ge empty_env le m (resVar i t) (cval v) :=
  eval_global_vt (hE.res i hi t ht) hl

theorem exec_res_store (hE : EnvOk E) {le : temp_env} {m : mem} {i : Nat} {t : VT} {e : expr}
    {v : Value} (hi : i < E.nres) (ht : t.isRes = true) (htv : t.has v = true)
    (he : eval_expr A E.ge empty_env le m e (cval v)) (hty : typeof e = t.ty)
    (hva : Mem.valid_access m t.chunk (E.res i t) 0 .Writable) :
    exec_stmt A X E.ge empty_env le m (.Sassign (resVar i t) e) E0 le
      (Mem.stored t.chunk m (E.res i t) 0 (cval v)) .Out_normal :=
  exec_assign_vt htv (hE.res i hi t ht) he hty hva

theorem StoreRel.store_res {α : Type} {st : Store α} {m : mem} (hE : EnvOk E)
    (h : StoreRel E st m) {i : Nat} {t : VT} (hi : i < E.nres) (ht : t.isRes = true)
    (chunk : memory_chunk) (ofs : _root_.Int) (v : val) :
    StoreRel E st (Mem.stored chunk m (E.res i t) ofs v) := by
  obtain ⟨-, hp, hm, hg, -⟩ := hE.res_other i hi t ht
  exact ⟨GlobalsRel.sameExcept h.1 (Mem.SameExcept.of_stored _ _ _ _ _) hg,
    h.2.store_other _ hp hm _ _⟩

theorem StatusRel.store_res {m : mem} {k : Nat} (hE : EnvOk E) (h : StatusRel E m k) {i : Nat}
    {t : VT} (hi : i < E.nres) (ht : t.isRes = true) (chunk : memory_chunk) (ofs : _root_.Int)
    (v : val) : StatusRel E (Mem.stored chunk m (E.res i t) ofs v) k :=
  h.sameExcept (Mem.SameExcept.of_stored _ _ _ _ _) (Ne.symm (hE.res_other i hi t ht).1)

theorem seqList_cons_ne (s : statement) {L : List statement} (h : L ≠ []) :
    seqList (s :: L) = .Ssequence s (seqList L) := by
  cases L with
  | nil => exact absurd rfl h
  | cons _ _ => rfl

/-- The stores of `resStores rs i h` and the `return` after them, from slots that hold `ws`:
the result globals from position `i` up then hold `ws`, and those below `i` keep their
values. -/
theorem exec_resStores (hE : EnvOk E) {α : Type} {st : Store α} {le : temp_env} :
    ∀ (rs : List VT) (i h : Nat) (ws : List Value) (m : mem),
      i + rs.length ≤ E.nres → rs.all VT.isRes = true → ArgsRel le h rs ws →
      StoreRel E st m → StatusRel E m 0 →
      ∃ m', exec_stmt A X E.ge empty_env le m (seqList (resStores rs i h ++ [.Sreturn none])) E0
          le m' (.Out_return none) ∧ StoreRel E st m' ∧ StatusRel E m' 0 ∧
        (∀ j (hj : j < rs.length), ∃ v, ws[j]? = some v ∧ rs[j].has v = true ∧
          Mem.load rs[j].chunk m' (E.res (i + j) rs[j]) 0 = some (cval v)) ∧
        ∀ j < i, ∀ t : VT, t.isRes = true →
          Mem.load t.chunk m' (E.res j t) 0 = Mem.load t.chunk m (E.res j t) 0
  | [], i, h, ws, m, _, _, hargs, hst, hs => by
      cases ws with
      | cons _ _ => simp [ArgsRel] at hargs
      | nil =>
          exact ⟨m, .exec_Sreturn_none _ _ _, hst, hs, fun j hj => absurd hj (by simp),
            fun _ _ _ _ => rfl⟩
  | t :: rs, i, h, ws, m, hn, hint, hargs, hst, hs => by
      cases ws with
      | nil => simp [ArgsRel] at hargs
      | cons w ws =>
          obtain ⟨htw, hslot, hrest⟩ := hargs
          simp only [List.all_cons, Bool.and_eq_true] at hint
          obtain ⟨ht, hint⟩ := hint
          simp only [List.length_cons] at hn
          have hi : i < E.nres := by omega
          have hva := hst.2.resW i hi t ht
          have hx1 := exec_res_store (A := A) (X := X) hE (le := le) hi ht htw
            (.eval_Etempvar _ _ _ hslot) rfl hva
          obtain ⟨m', hx2, hst', hs', hload, hframe⟩ := exec_resStores hE rs (i + 1) (h + 1) ws
            (Mem.stored t.chunk m (E.res i t) 0 (cval w)) (by omega) hint hrest
            (hst.store_res hE hi ht _ _ _) (hs.store_res hE hi ht _ _ _)
          refine ⟨m', ?_, hst', hs', fun j hj => ?_, fun j hj t' ht' => ?_⟩
          · rw [show resStores (t :: rs) i h ++ [.Sreturn none] =
                .Sassign (resVar i t) (tmp h t) :: (resStores rs (i + 1) (h + 1) ++ [.Sreturn none])
                from rfl, seqList_cons_ne _ (by simp)]
            exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ hx1 hx2
          · cases j with
            | zero =>
                refine ⟨w, rfl, htw, ?_⟩
                show Mem.load t.chunk m' (E.res i t) 0 = some (cval w)
                rw [hframe i (by omega) t ht]
                exact load_stored_vt htw hva
            | succ j =>
                obtain ⟨v, hv, htv, hl⟩ := hload j (by simp at hj; omega)
                refine ⟨v, hv, htv, ?_⟩
                rw [show i + (j + 1) = i + 1 + j by omega]
                exact hl
          · rw [hframe j (by omega) t' ht']
            have hne : E.res i t ≠ E.res j t' := fun e =>
              absurd (hE.res_inj i j t t' hi (by omega) ht ht' e).1 (by omega)
            exact Mem.load_stored_other _ _ _ _ _ _ _ _ hne

/-- The copies of `resLoads rs i h` from result globals that hold `ws`: the slots from height
`h` up then hold `ws`, and every other temporary keeps its value. -/
theorem exec_resLoads (hE : EnvOk E) {m : mem} :
    ∀ (rs : List VT) (i h : Nat) (ws : List Value) (le : temp_env), rs ≠ [] →
      i + rs.length ≤ E.nres → rs.all VT.isRes = true → ws.length = rs.length →
      (∀ j (hj : j < rs.length), ∃ v, ws[j]? = some v ∧ rs[j].has v = true ∧
        Mem.load rs[j].chunk m (E.res (i + j) rs[j]) 0 = some (cval v)) →
      ∃ le', exec_stmt A X E.ge empty_env le m (seqList (resLoads rs i h)) E0 le' m .Out_normal ∧
        ArgsRel le' h rs ws ∧
        ∀ id, (∀ j < rs.length, ∀ t, id ≠ slotId (h + j) t) → le'[id]? = le[id]?
  | [], _, _, _, _, hne, _, _, _, _ => absurd rfl hne
  | t :: rs, i, h, ws, le, _, hn, hint, hlen, hload => by
      cases ws with
      | nil => simp at hlen
      | cons w ws =>
          simp only [List.all_cons, Bool.and_eq_true] at hint
          obtain ⟨ht, hint⟩ := hint
          simp only [List.length_cons] at hn hlen
          obtain ⟨v0, hv0, htv0, hl0⟩ := hload 0 (by simp)
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv0
          rw [← hv0] at htv0 hl0
          have hev := eval_res (A := A) hE (le := le) (by omega) ht hl0
          let le1 := le.insert (slotId h t) (cval w)
          cases rs with
          | nil =>
              cases ws with
              | cons _ _ => simp at hlen
              | nil =>
                  refine ⟨le1, .exec_Sset _ _ _ _ _ _ hev, ⟨htv0, te_insert_same _ _ _, trivial⟩,
                    fun id hid => ?_⟩
                  exact te_insert_ne _ (Ne.symm (hid 0 (by simp) t))
          | cons t2 rs =>
              obtain ⟨le', hx, hargs, hother⟩ := exec_resLoads hE (t2 :: rs) (i + 1) (h + 1) ws le1
                (by simp) (by simp at hn ⊢; omega) hint (by simpa using hlen)
                (fun j hj => by
                  obtain ⟨v, hv, htv, hl⟩ := hload (j + 1) (by simp at hj ⊢; omega)
                  exact ⟨v, by simpa using hv, by simpa using htv, by
                    rw [show i + 1 + j = i + (j + 1) by omega]; simpa using hl⟩)
              refine ⟨le', ?_, ⟨htv0, ?_, hargs⟩, fun id hid => ?_⟩
              · rw [show resLoads (t :: t2 :: rs) i h =
                    .Sset (slotId h t) (resVar i t) :: resLoads (t2 :: rs) (i + 1) (h + 1)
                    from rfl, seqList_cons_ne _ (by simp [resLoads])]
                exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sset _ _ _ _ _ _ hev) hx
              · rw [hother _ (fun j _ t' => slotId_ne_of_height _ _ (by omega))]
                exact te_insert_same _ _ _
              · rw [hother _ (fun j hj t' => by
                  have := hid (j + 1) (by simp at hj ⊢; omega) t'
                  rw [show h + (j + 1) = h + 1 + j by omega] at this
                  exact this)]
                exact te_insert_ne _ (Ne.symm (hid 0 (by simp) t))

theorem eval_res_any (hE : EnvOk E) {le : temp_env} {m : mem} {i : Nat} {t : VT}
    (hi : i < E.nres) (ht : t.isRes = true)
    (hva : Mem.valid_access m t.chunk (E.res i t) 0 .Writable) :
    ∃ v, eval_expr A E.ge empty_env le m (resVar i t) v := by
  have hl : Mem.load t.chunk m (E.res i t) 0 =
      some (decode_val t.chunk (Mem.getN (size_chunk_nat t.chunk) 0
        (Mem.contents_of m (E.res i t)))) := by
    unfold Mem.load
    rw [ite_eq_left (Mem.valid_access_readable hva)]
  refine ⟨decode_val t.chunk (Mem.getN (size_chunk_nat t.chunk) 0
      (Mem.contents_of m (E.res i t))),
    .eval_Elvalue _ _ _ _ _ (eval_lvalue_global (hE.res i hi t ht))
      (.deref_loc_value t.chunk _ ?_ ?_)⟩
  · exact VT.access t
  · rw [loadv_zero _ _ _ (VT.size_chunk_le t)]
    exact hl

/-- The copies of `resLoads` run whatever the result globals hold. -/
theorem exec_resLoads_any (hE : EnvOk E) {m : mem}
    (hW : ∀ i < E.nres, ∀ t : VT, t.isRes = true →
      Mem.valid_access m t.chunk (E.res i t) 0 .Writable) :
    ∀ (rs : List VT) (i h : Nat) (le : temp_env), rs ≠ [] → i + rs.length ≤ E.nres →
      rs.all VT.isRes = true →
      ∃ le', exec_stmt A X E.ge empty_env le m (seqList (resLoads rs i h)) E0 le' m .Out_normal
  | [], _, _, _, hne, _, _ => absurd rfl hne
  | t :: rs, i, h, le, _, hn, hint => by
      simp only [List.all_cons, Bool.and_eq_true] at hint
      obtain ⟨ht, hint⟩ := hint
      simp only [List.length_cons] at hn
      obtain ⟨v, hev⟩ := eval_res_any (A := A) hE (le := le) (by omega) ht (hW i (by omega) t ht)
      cases rs with
      | nil => exact ⟨_, .exec_Sset _ _ _ _ _ _ hev⟩
      | cons t2 rs =>
          obtain ⟨le', hx⟩ := exec_resLoads_any hE hW (t2 :: rs) (i + 1) (h + 1)
            (le.insert (slotId h t) v) (by simp) (by simp at hn ⊢; omega) hint
          refine ⟨le', ?_⟩
          rw [show resLoads (t :: t2 :: rs) i h =
              .Sset (slotId h t) (resVar i t) :: resLoads (t2 :: rs) (i + 1) (h + 1)
              from rfl, seqList_cons_ne _ (by simp [resLoads])]
          exact .exec_Sseq_1 _ _ _ _ _ _ _ _ _ _ _ _ (.exec_Sset _ _ _ _ _ _ hev) hx

end

end LeanExe.Native
