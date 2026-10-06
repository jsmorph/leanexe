import LeanExe.WGSL.Translate
import LeanExe.IR.DenoteStmt

/-!
The translation of IR statements built from assignments, sequences, and the compiler's loops into
WGSL, and its simulation lemma.  An assignment becomes the expression's `let` statements and an
assignment to the local's `var`; a loop on `ltU (get index) (get limit)` becomes a `while` on
`lt64`, which runs in lockstep with the denotation's loop under the same bound.
-/

namespace LeanExe.WGSL

/-- The WGSL type of an IR scalar type. -/
def wgslTy : LeanExe.IR.ScalarType → Ty
  | .u64 => .vec2u
  | .f32 => .f32
  | .bool => .bool
  | .f64 => .vec2u

theorem wgslTy_holds (type : LeanExe.IR.ScalarType) (v : type.denote) :
    (wgslTy type).holds (wgslValue type v) = true := by
  cases type <;> rfl

theorem sameType_of_holds {type : LeanExe.IR.ScalarType} {old : Value} (v : type.denote)
    (h : (wgslTy type).holds old = true) : old.sameType (wgslValue type v) = true := by
  cases type <;> cases old <;> simp_all [wgslTy, Ty.holds, wgslValue, pairOf, Value.sameType]

/-- The condition of a compiled loop, `ltU (get index) (get limit)`, as one expression. -/
def trCond (F : Layout) : LeanExe.IR.Expr .bool → Option Expr
  | .ltU (.get i) (.get l) => do pure (lt64 (← F.scalar i) (← F.scalar l))
  | _ => none

/-- The statements of an IR statement from variable `next` on, and the next free variable;
`none` outside the translated subset. -/
def trStmt (F : Layout) : LeanExe.IR.Stmt → Nat → Option (List Stmt × Nat)
  | .skip, next => some ([], next)
  | .assign (type := type) j e, next => do
      let w ← F.scalar j
      if F.assigned j = some type then
        let (stmts, res, next') ← trExpr F e next
        pure (stmts ++ [.assign w (.var res)], next')
      else none
  | .seq a b, next => do
      let (sa, n1) ← trStmt F a next
      let (sb, n2) ← trStmt F b n1
      pure (sa ++ sb, n2)
  | .while c body, next => do
      let ce ← trCond F c
      let (sb, n1) ← trStmt F body next
      pure ([.while_ ce sb], n1)
  | _, _ => none

/-- Every variable of the layout is below `n`. -/
def Layout.Below (F : Layout) (n : Nat) : Prop :=
  (∀ j w, F.scalar j = some w → w < n) ∧ (∀ a b len, F.array a = some (b, len) → len < n)

/-- An assigned local has its own variable, which no other local and no array length uses. -/
structure Layout.Distinct (F : Layout) : Prop where
  scalar : ∀ j j' type w, F.assigned j = some type → F.scalar j = some w →
    F.scalar j' = some w → j' = j
  array : ∀ j type w a b len, F.assigned j = some type → F.scalar j = some w →
    F.array a = some (b, len) → len ≠ w

/-- Each assigned local's variable is a `var` that holds a value of its type. -/
def Layout.Writable (F : Layout) (env : Env) : Prop :=
  ∀ j type, F.assigned j = some type →
    ∃ w old, F.scalar j = some w ∧ env.find w = some (old, true) ∧ (wgslTy type).holds old = true

/-- Two environments with the same names and kinds in the same order. -/
def Env.Shape (a b : Env) : Prop := a.map (fun x => (x.1, x.2.2)) = b.map (fun x => (x.1, x.2.2))

theorem Env.Shape.refl (a : Env) : Env.Shape a a := rfl

theorem Env.Shape.trans {a b c : Env} (h1 : Env.Shape a b) (h2 : Env.Shape b c) : Env.Shape a c :=
  Eq.trans h1 h2

theorem Env.Shape.length {a b : Env} (h : Env.Shape a b) : a.length = b.length := by
  have := congrArg List.length h
  simpa using this

theorem Env.Shape.find_none {a b : Env} (h : Env.Shape a b) (w : Nat) (hb : b.find w = none) :
    a.find w = none := by
  induction a generalizing b with
  | nil => rfl
  | cons x a ih =>
      cases b with
      | nil => simp [Env.Shape] at h
      | cons y b =>
          obtain ⟨n, val, flag⟩ := x
          obtain ⟨n', val', flag'⟩ := y
          simp only [Env.Shape, List.map_cons, List.cons.injEq, Prod.mk.injEq] at h
          obtain ⟨⟨rfl, rfl⟩, h⟩ := h
          by_cases hn : n = w
          · subst hn
            rw [Env.find_cons_self] at hb
            cases hb
          · rw [Env.find_cons_ne _ _ _ _ _ hn] at hb ⊢
            exact ih h hb

theorem Env.Shape.append {a b : Env} (c : Env) (h : Env.Shape a b) : Env.Shape (c ++ a) (c ++ b) := by
  simp only [Env.Shape, List.map_append] at h ⊢
  rw [h]

theorem Env.Shape.split {e x y : Env} (h : Env.Shape e (x ++ y)) :
    ∃ a b, e = a ++ b ∧ Env.Shape a x ∧ Env.Shape b y := by
  simp only [Env.Shape, List.map_append] at h
  obtain ⟨a, b, rfl, ha, hb⟩ := List.map_eq_append_iff.mp h
  exact ⟨a, b, rfl, ha, hb⟩

theorem Env.set_shape (env : Env) (w : Nat) (v : Value) : Env.Shape (env.set w v) env := by
  unfold Env.Shape Env.set
  rw [List.map_map]
  apply List.map_congr_left
  intro x _
  obtain ⟨n, val, flag⟩ := x
  by_cases hn : n = w <;> simp [hn]

theorem Env.set_cons_same (env : Env) (w : Nat) (v val : Value) (flag : Bool) :
    Env.set ((w, val, flag) :: env) w v = (w, v, flag) :: env.set w v := by
  simp [Env.set]

theorem Env.set_cons_ne (env : Env) {n w : Nat} (v val : Value) (flag : Bool) (h : n ≠ w) :
    Env.set ((n, val, flag) :: env) w v = (n, val, flag) :: env.set w v := by
  simp [Env.set, h]

theorem Env.find_set_same {env : Env} {w : Nat} {old v : Value} {m : Bool}
    (h : env.find w = some (old, m)) : (env.set w v).find w = some (v, m) := by
  induction env with
  | nil => simp [Env.find] at h
  | cons x env ih =>
      obtain ⟨n, val, flag⟩ := x
      by_cases hx : n = w
      · subst hx
        rw [Env.find_cons_self] at h
        obtain ⟨-, rfl⟩ := Prod.mk.inj (Option.some.inj h)
        rw [Env.set_cons_same, Env.find_cons_self]
      · rw [Env.find_cons_ne env n w val flag hx] at h
        rw [Env.set_cons_ne env v val flag hx, Env.find_cons_ne _ n w val flag hx]
        exact ih h

theorem Env.find_set_ne (env : Env) {w w' : Nat} (v : Value) (hne : w' ≠ w) :
    (env.set w v).find w' = env.find w' := by
  induction env with
  | nil => rfl
  | cons x env ih =>
      obtain ⟨n, val, flag⟩ := x
      by_cases hx : n = w
      · subst hx
        rw [Env.set_cons_same, Env.find_cons_ne _ n w' v flag (Ne.symm hne),
          Env.find_cons_ne _ n w' val flag (Ne.symm hne), ih]
      · rw [Env.set_cons_ne env v val flag hx]
        by_cases hx' : n = w'
        · subst hx'
          rw [Env.find_cons_self, Env.find_cons_self]
        · rw [Env.find_cons_ne _ n w' val flag hx', Env.find_cons_ne _ n w' val flag hx', ih]

theorem Env.Shape.names {a b : Env} (h : Env.Shape a b) : ∀ x ∈ a, ∃ y ∈ b, y.1 = x.1 := by
  intro x hx
  have : (x.1, x.2.2) ∈ b.map (fun x => (x.1, x.2.2)) := by
    rw [← h]; exact List.mem_map_of_mem hx
  obtain ⟨y, hy, hxy⟩ := List.mem_map.mp this
  exact ⟨y, hy, by simp only [Prod.mk.injEq] at hxy; exact hxy.1⟩

theorem Layout.Agrees.drop {F : Layout} {L : Nat → Option Wasm.Value}
    {arrays : Nat → Option (Array UInt64)} {ctx : Context} {a b : Env} {n : Nat}
    (hB : F.Below n) (ha : ∀ x ∈ a, n ≤ x.1) (h : F.Agrees L arrays ctx (a ++ b)) :
    F.Agrees L arrays ctx b := by
  have keep : ∀ w, w < n → Env.find (a ++ b) w = Env.find b w := fun w hw =>
    Env.find_append_fresh a b w (fun x hx h => by have := ha x hx; omega)
  refine ⟨fun j v hj => ?_, fun j v hj => ?_, fun c xs hc => ?_⟩
  · obtain ⟨w, m, hw, hf⟩ := h.word j v hj
    exact ⟨w, m, hw, (keep w (hB.1 j w hw)) ▸ hf⟩
  · obtain ⟨w, m, hw, hf⟩ := h.float j v hj
    exact ⟨w, m, hw, (keep w (hB.1 j w hw)) ▸ hf⟩
  · obtain ⟨hs, bb, len, hF, hbuf, hl⟩ := h.array c xs hc
    exact ⟨hs, bb, len, hF, hbuf, (keep len (hB.2 c bb len hF)) ▸ hl⟩

theorem Layout.Writable.drop {F : Layout} {a b : Env} {n : Nat}
    (hB : F.Below n) (ha : ∀ x ∈ a, n ≤ x.1) (h : F.Writable (a ++ b)) : F.Writable b := by
  intro j type hj
  obtain ⟨w, old, hw, hf, ht⟩ := h j type hj
  refine ⟨w, old, hw, ?_, ht⟩
  rw [← Env.find_append_fresh a b w (fun x hx h => by have := ha x hx; have := hB.1 j w hw; omega)]
  exact hf

theorem Layout.Writable.extend {F : Layout} {a b : Env} {n : Nat}
    (hB : F.Below n) (ha : ∀ x ∈ a, n ≤ x.1) (h : F.Writable b) : F.Writable (a ++ b) := by
  intro j type hj
  obtain ⟨w, old, hw, hf, ht⟩ := h j type hj
  refine ⟨w, old, hw, ?_, ht⟩
  rw [Env.find_append_fresh a b w (fun x hx h => by have := ha x hx; have := hB.1 j w hw; omega)]
  exact hf

theorem Layout.Below.mono {F : Layout} {n n' : Nat} (h : F.Below n) (hle : n ≤ n') : F.Below n' :=
  ⟨fun j w hw => by have := h.1 j w hw; omega, fun a b len hF => by have := h.2 a b len hF; omega⟩

/-- What running a statement's translation leaves: new bindings named from `next` below `next'`
in front of an environment with the old names and kinds, which agrees with the denoted locals. -/
def StmtSim (F : Layout) (L' : Nat → Option Wasm.Value) (arrays : Nat → Option (Array UInt64))
    (ctx : Context) (env : Env) (writes : List (Nat × UInt32)) (stmts : List Stmt)
    (next next' : Nat) : Prop :=
  ∃ added E, Stmt.execList ctx ⟨env, writes, false⟩ stmts = some ⟨added ++ E, writes, false⟩ ∧
    Env.Shape E env ∧ (∀ b ∈ added, next ≤ b.1 ∧ b.1 < next') ∧
    F.Agrees L' arrays ctx E ∧ F.Writable E

theorem trStmt_mono (F : Layout) :
    ∀ (s : LeanExe.IR.Stmt) (next : Nat) (stmts : List Stmt) (next' : Nat),
      trStmt F s next = some (stmts, next') → next ≤ next' := by
  intro s
  induction s with
  | skip => intro next stmts next' h; simp only [trStmt, Option.some.injEq, Prod.mk.injEq] at h; omega
  | assign j e =>
      intro next stmts next' h
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hw : F.scalar j with
      | none => simp [hw] at h
      | some w =>
        simp only [hw, Option.bind_some] at h
        split at h
        · cases ht : trExpr F e next with
          | none => simp [ht] at h
          | some r =>
            obtain ⟨st, res, n'⟩ := r
            simp only [ht, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            have := trExpr_mono F e _ _ _ _ ht
            omega
        · cases h
  | seq a b iha ihb =>
      intro next stmts next' h
      simp only [trStmt, Option.bind_eq_bind] at h
      cases ha : trStmt F a next with
      | none => simp [ha] at h
      | some ra =>
        obtain ⟨sa, n1⟩ := ra
        cases hb : trStmt F b n1 with
        | none => simp [ha, hb] at h
        | some rb =>
          obtain ⟨sb, n2⟩ := rb
          simp only [ha, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          have := iha _ _ _ ha
          have := ihb _ _ _ hb
          omega
  | «while» c body ih =>
      intro next stmts next' h
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hc : trCond F c with
      | none => simp [hc] at h
      | some ce =>
        cases hb : trStmt F body next with
        | none => simp [hc, hb] at h
        | some rb =>
          obtain ⟨sb, n1⟩ := rb
          simp only [hc, hb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          have := ih _ _ _ hb
          omega
  | _ =>
      intro next stmts next' h
      simp [trStmt] at h

theorem trCond_inv {F : Layout} {c : LeanExe.IR.Expr .bool} {ce : Expr} (h : trCond F c = some ce) :
    ∃ i l wi wl, c = .ltU (.get i) (.get l) ∧ F.scalar i = some wi ∧ F.scalar l = some wl ∧
      ce = lt64 wi wl := by
  unfold trCond at h
  split at h
  · rename_i i l
    cases hi : F.scalar i with
    | none => simp [hi] at h
    | some wi =>
      cases hl : F.scalar l with
      | none => simp [hi, hl] at h
      | some wl =>
        simp only [hi, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def,
          Option.some.injEq] at h
        exact ⟨i, l, wi, wl, rfl, hi, hl, h.symm⟩
  · cases h

/-- The `while` statement's test and the run of its body, which drops the body's declarations. -/
theorem exec_while (ctx : Context) (run : Run) (c : Expr) (body : List Stmt) :
    Stmt.exec ctx run (.while_ c body) =
      loopRuns (fun r => match c.eval ctx r.env with
          | some (.bool b) => some b
          | _ => none)
        (fun r => (Stmt.execList ctx r body).map fun inner =>
          { inner with env := inner.env.drop (inner.env.length - r.env.length) })
        loopBound run := by
  rw [Stmt.exec]
  rfl

/-- Running the translation of a statement whose denotation succeeds leaves an environment that
agrees with the denoted locals. -/
theorem trStmt_sim (F : Layout) (hD : F.Distinct) (arrays : Nat → Option (Array UInt64))
    (ctx : Context) (writes : List (Nat × UInt32)) :
    ∀ (s : LeanExe.IR.Stmt) (next : Nat) (stmts : List Stmt) (next' : Nat),
      trStmt F s next = some (stmts, next') → F.Below next →
      ∀ L L', s.denote arrays L = some L' →
      ∀ env, F.Agrees L arrays ctx env → F.Writable env → (∀ n, next ≤ n → env.find n = none) →
      StmtSim F L' arrays ctx env writes stmts next next' := by
  intro s
  induction s with
  | skip =>
      intro next stmts next' htr _ L L' hden env hA hW _
      simp only [trStmt, Option.some.injEq, Prod.mk.injEq] at htr
      obtain ⟨rfl, rfl⟩ := htr
      simp only [LeanExe.IR.Stmt.denote, Option.some.injEq] at hden
      subst hden
      exact ⟨[], env, by simp [Stmt.execList], Env.Shape.refl _, by simp, hA, hW⟩
  | assign j e =>
      rename_i type
      intro next stmts next' htr hB L L' hden env hA hW hFresh
      simp only [trStmt, Option.bind_eq_bind] at htr
      cases hw : F.scalar j with
      | none => simp [hw] at htr
      | some w =>
        simp only [hw, Option.bind_some] at htr
        split at htr
        · rename_i hty
          cases ht : trExpr F e next with
          | none => simp [ht] at htr
          | some r =>
            obtain ⟨st, res, n'⟩ := r
            simp only [ht, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at htr
            obtain ⟨rfl, rfl⟩ := htr
            simp only [LeanExe.IR.Stmt.denote] at hden
            split at hden
            · obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hden
              obtain ⟨added, hrun, hb, -, -, m, hf⟩ :=
                trExpr_sim F L arrays ctx writes e next st res n' ht v hv env hA hFresh
              obtain ⟨w', old, hw', hold, hholds⟩ := hW j type hty
              rw [hw] at hw'
              cases hw'
              have hwlt : w < next := hB.1 j w hw
              have hold' : Env.find (added ++ env) w = some (old, true) := by
                rw [Env.find_append_fresh added env w (fun b hb' h => by have := hb b hb'; omega)]
                exact hold
              have hset : (added ++ env).set w (wgslValue type v) =
                  added ++ env.set w (wgslValue type v) := by
                rw [Env.set_append, Env.set_fresh added w _
                  (fun b hb' h => by have := hb b hb'; omega)]
              refine ⟨added, env.set w (wgslValue type v), ?_, Env.set_shape _ _ _, hb, ?_, ?_⟩
              · rw [execList_append, hrun, Option.bind_some]
                simp [Stmt.execList, Stmt.exec, Expr.eval, hf, hold', sameType_of_holds v hholds,
                  hset]
              · refine ⟨fun i u hi => ?_, fun i u hi => ?_, fun a xs ha => ?_⟩
                · by_cases hij : i = j
                  · subst hij
                    simp only [↓reduceIte, Option.some.injEq] at hi
                    cases type <;> simp only [LeanExe.IR.ScalarType.value, reduceCtorEq,
                      Wasm.Value.i64.injEq] at hi
                    subst hi
                    exact ⟨w, true, hw, Env.find_set_same hold⟩
                  · simp only [hij, ↓reduceIte] at hi
                    obtain ⟨wi, mi, hwi, hfi⟩ := hA.word i u hi
                    have hne : wi ≠ w := fun h => hij (hD.scalar j i type w hty hw (h ▸ hwi))
                    exact ⟨wi, mi, hwi, by rw [Env.find_set_ne env _ hne]; exact hfi⟩
                · by_cases hij : i = j
                  · subst hij
                    simp only [↓reduceIte, Option.some.injEq] at hi
                    cases type <;> simp only [LeanExe.IR.ScalarType.value, reduceCtorEq,
                      Wasm.Value.f32.injEq] at hi
                    subst hi
                    exact ⟨w, true, hw, Env.find_set_same hold⟩
                  · simp only [hij, ↓reduceIte] at hi
                    obtain ⟨wi, mi, hwi, hfi⟩ := hA.float i u hi
                    have hne : wi ≠ w := fun h => hij (hD.scalar j i type w hty hw (h ▸ hwi))
                    exact ⟨wi, mi, hwi, by rw [Env.find_set_ne env _ hne]; exact hfi⟩
                · obtain ⟨hs, b, len, hF, hbuf, hl⟩ := hA.array a xs ha
                  have hne : len ≠ w := hD.array j type w a b len hty hw hF
                  exact ⟨hs, b, len, hF, hbuf, by rw [Env.find_set_ne env _ hne]; exact hl⟩
              · intro j2 type2 hj2
                obtain ⟨w2, old2, hw2, hf2, ht2⟩ := hW j2 type2 hj2
                by_cases hww : w2 = w
                · subst hww
                  obtain rfl : j2 = j := hD.scalar j j2 type w2 hty hw hw2
                  rw [hty] at hj2
                  cases hj2
                  exact ⟨w2, wgslValue type v, hw2, Env.find_set_same hf2, wgslTy_holds type v⟩
                · exact ⟨w2, old2, hw2, by rw [Env.find_set_ne env _ hww]; exact hf2, ht2⟩
            · cases hden
        · cases htr
  | seq a b iha ihb =>
      intro next stmts next' htr hB L L' hden env hA hW hFresh
      simp only [trStmt, Option.bind_eq_bind] at htr
      cases hta : trStmt F a next with
      | none => simp [hta] at htr
      | some ra =>
        obtain ⟨sa, n1⟩ := ra
        cases htb : trStmt F b n1 with
        | none => simp [hta, htb] at htr
        | some rb =>
          obtain ⟨sb, n2⟩ := rb
          simp only [hta, htb, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl⟩ := htr
          simp only [LeanExe.IR.Stmt.denote, Option.bind_eq_some_iff] at hden
          obtain ⟨L1, hda, hdb⟩ := hden
          have hle1 := trStmt_mono F a _ _ _ hta
          obtain ⟨added1, E1, hrun1, hS1, hb1, hA1, hW1⟩ :=
            iha next sa n1 hta hB L L1 hda env hA hW hFresh
          have hE1 : ∀ x ∈ E1, x.1 < next := fun x hx => by
            obtain ⟨y, hy, hxy⟩ := hS1.names x hx
            have := names_lt hFresh y hy
            omega
          have hFresh1 : ∀ n, n1 ≤ n → Env.find (added1 ++ E1) n = none :=
            find_none_of_names fun x hx => by
              rcases List.mem_append.mp hx with hx | hx
              · exact (hb1 x hx).2
              · have := hE1 x hx; omega
          have hA1' : F.Agrees L1 arrays ctx (added1 ++ E1) := hA1.extend added1 fun x hx =>
            find_none_of_names hE1 x.1 (hb1 x hx).1
          have hW1' := hW1.extend hB fun x hx => (hb1 x hx).1
          obtain ⟨added2, E2, hrun2, hS2, hb2, hA2, hW2⟩ :=
            ihb n1 sb n2 htb (hB.mono hle1) L1 L' hdb (added1 ++ E1) hA1' hW1' hFresh1
          obtain ⟨A, B, rfl, hSA, hSB⟩ := hS2.split
          have hAnames : ∀ x ∈ A, next ≤ x.1 ∧ x.1 < n1 := fun x hx => by
            obtain ⟨y, hy, hxy⟩ := hSA.names x hx
            have := hb1 y hy
            omega
          have hle2 := trStmt_mono F b _ _ _ htb
          refine ⟨added2 ++ A, B, ?_, hSB.trans hS1, ?_, hA2.drop hB fun x hx => (hAnames x hx).1,
            hW2.drop hB fun x hx => (hAnames x hx).1⟩
          · rw [execList_append, hrun1, Option.bind_some, hrun2]
            simp
          · intro x hx
            rcases List.mem_append.mp hx with hx | hx
            · exact ⟨by have := (hb2 x hx).1; omega, (hb2 x hx).2⟩
            · have := hAnames x hx; omega
  | «while» c body ih =>
      intro next stmts next' htr hB L L' hden env hA hW hFresh
      simp only [trStmt, Option.bind_eq_bind] at htr
      cases hc : trCond F c with
      | none => simp [hc] at htr
      | some ce =>
        cases hbt : trStmt F body next with
        | none => simp [hc, hbt] at htr
        | some rb =>
          obtain ⟨sb, n1⟩ := rb
          simp only [hc, hbt, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl⟩ := htr
          obtain ⟨i, l, wi, wl, rfl, hwi, hwl, rfl⟩ := trCond_inv hc
          simp only [LeanExe.IR.Stmt.denote] at hden
          have key : ∀ fuel Lc E, Env.Shape E env → F.Agrees Lc arrays ctx E → F.Writable E →
              LeanExe.IR.loopIter (fun l' => (LeanExe.IR.Expr.ltU (.get i) (.get l)).denote l' arrays)
                (LeanExe.IR.Stmt.denote arrays body) fuel Lc = some L' →
              ∃ E', loopRuns (fun r => match (lt64 wi wl).eval ctx r.env with
                  | some (.bool b) => some b
                  | _ => none)
                (fun r => (Stmt.execList ctx r sb).map fun inner =>
                  { inner with env := inner.env.drop (inner.env.length - r.env.length) })
                fuel ⟨E, writes, false⟩ = some ⟨E', writes, false⟩ ∧
              Env.Shape E' env ∧ F.Agrees L' arrays ctx E' ∧ F.Writable E' := by
            intro fuel
            induction fuel with
            | zero => intro Lc E _ _ _ h; cases h
            | succ fuel ihf =>
                intro Lc E hS hAc hWc hI
                rw [LeanExe.IR.loopIter_succ] at hI
                cases hcd : (LeanExe.IR.Expr.ltU (.get i) (.get l)).denote Lc arrays with
                | none => simp [hcd] at hI
                | some b =>
                  obtain ⟨x, y, hx, hy, rfl⟩ : ∃ x y, Lc i = some (.i64 x) ∧ Lc l = some (.i64 y) ∧
                      b = decide (x < y) := by
                    simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hcd
                    split at hcd
                    · rename_i x hx
                      split at hcd
                      · rename_i y hy
                        simp only [Option.bind_some, Option.some.injEq] at hcd
                        exact ⟨x, y, hx, hy, hcd.symm⟩
                      · simp at hcd
                    · simp at hcd
                  obtain ⟨wi', mi, hwi', hfi⟩ := hAc.word i x hx
                  rw [hwi] at hwi'
                  cases hwi'
                  obtain ⟨wl', ml, hwl', hfl⟩ := hAc.word l y hy
                  rw [hwl] at hwl'
                  cases hwl'
                  have htest := lt64_word ctx E wi wl x y hfi hfl
                  simp only [hcd, Option.bind_some] at hI
                  cases hxy : decide (x < y)
                  · simp only [hxy, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at hI
                    subst hI
                    exact ⟨E, by simp [loopRuns, htest, hxy], hS, hAc, hWc⟩
                  · simp only [hxy, ↓reduceIte] at hI
                    cases hbd : LeanExe.IR.Stmt.denote arrays body Lc with
                    | none => simp [hbd] at hI
                    | some Lc1 =>
                      simp only [hbd, Option.bind_some] at hI
                      obtain ⟨added, E1, hrun, hS1, -, hA1, hW1⟩ :=
                        ih next sb n1 hbt hB Lc Lc1 hbd E hAc hWc (fun n hn =>
                          hS.find_none n (hFresh n hn))
                      obtain ⟨E', hrun', hS', hA', hW'⟩ := ihf Lc1 E1 (hS1.trans hS) hA1 hW1 hI
                      refine ⟨E', ?_, hS', hA', hW'⟩
                      have hdrop : List.drop (added.length + E1.length - E.length) (added ++ E1) =
                          E1 := by
                        rw [hS1.length, Nat.add_sub_cancel, List.drop_left]
                      simp [loopRuns, htest, hxy, hrun, hdrop, hrun']
          obtain ⟨E', hrun, hS, hA', hW'⟩ := key loopBound L env (Env.Shape.refl _) hA hW hden
          refine ⟨[], E', ?_, hS, by simp, hA', hW'⟩
          simp [Stmt.execList, exec_while, hrun]
  | _ =>
      intro next stmts next' htr
      simp [trStmt] at htr

theorem trStmt_writes (F : Layout) :
    ∀ (s : LeanExe.IR.Stmt) (next : Nat) (stmts : List Stmt) (next' : Nat),
      trStmt F s next = some (stmts, next') → ∀ j ∈ s.writes, (F.assigned j).isSome := by
  intro s
  induction s with
  | assign i e =>
      intro next stmts next' h j hj
      simp only [LeanExe.IR.Stmt.writes, List.mem_singleton] at hj
      subst hj
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hw : F.scalar j with
      | none => simp [hw] at h
      | some w =>
        simp only [hw, Option.bind_some] at h
        split at h
        · rename_i hty; simp [hty]
        · cases h
  | seq a b iha ihb =>
      intro next stmts next' h j hj
      simp only [trStmt, Option.bind_eq_bind] at h
      cases ha : trStmt F a next with
      | none => simp [ha] at h
      | some ra =>
        cases hb : trStmt F b ra.2 with
        | none => simp [ha, hb] at h
        | some rb =>
          simp only [LeanExe.IR.Stmt.writes, List.mem_append] at hj
          rcases hj with hj | hj
          · exact iha _ _ _ ha j hj
          · exact ihb _ _ _ hb j hj
  | «while» c body ih =>
      intro next stmts next' h j hj
      simp only [trStmt, Option.bind_eq_bind] at h
      cases hc : trCond F c with
      | none => simp [hc] at h
      | some ce =>
        cases hb : trStmt F body next with
        | none => simp [hc, hb] at h
        | some rb => exact ih _ _ _ hb j hj
  | skip => intro next stmts next' _ j hj; simp [LeanExe.IR.Stmt.writes] at hj
  | _ => intro next stmts next' h; simp [trStmt] at h

theorem Env.find_of_mem {env : Env} (hnd : (env.map (·.1)).Nodup) {w : Nat} {v : Value} {m : Bool}
    (h : (w, v, m) ∈ env) : env.find w = some (v, m) := by
  induction env with
  | nil => cases h
  | cons x env ih =>
      obtain ⟨n, val, flag⟩ := x
      simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
      rcases List.mem_cons.mp h with h | h
      · simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        exact Env.find_cons_self _ _ _ _
      · have hne : n ≠ w := fun hn => hnd.1 ⟨(w, v, m), h, by simp [hn]⟩
        rw [Env.find_cons_ne _ _ _ _ _ hne]
        exact ih hnd.2 h

end LeanExe.WGSL
