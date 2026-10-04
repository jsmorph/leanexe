import Project.WGSL.Pair
import Project.IR.Denote

/-!
The translation of IR expressions of the kernel subset into WGSL `let` statements, one per node,
and its simulation lemma: from an environment that holds the IR locals and arrays the way a
`Layout` says, the statements run without error and leave the expression's denotation in the
result variable, a `u64` as the pair of its halves and a binary32 value as an `f32`.
-/

namespace Project.WGSL

/-- Where the translation finds each IR local: a scalar local's WGSL variable, and an array
pointer's buffer and the variable that holds the array's length as a pair.  The locals that
statements assign have types, and their variables are `var`s. -/
structure Layout where
  scalar : Nat → Option Nat
  array : Nat → Option (Nat × Nat)
  assigned : Nat → Option Project.IR.ScalarType := fun _ => none

def F32Op.wgsl : Project.IR.F32Op → BinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

def F32UnOp.wgsl : Project.IR.F32UnOp → Expr → Expr
  | .sqrt, e => .sqrt e
  | .abs, e => .abs e

/-- The pair operation of a `u64` operation, for those the translation covers. -/
def U64Op.wgsl? : Project.IR.U64Op → Option (Nat → Nat → Expr)
  | .add => some add64
  | .mul => some mul64
  | _ => none

/-- The statements that compute an IR expression from variable `next` on, the variable that holds
its value, and the next free variable; `none` outside the kernel subset. -/
def trExpr (F : Layout) : {type : Project.IR.ScalarType} → Project.IR.Expr type → Nat →
    Option (List Stmt × Nat × Nat)
  | .u64, .get j, next => (F.scalar j).map fun v => ([], v, next)
  | .u64, .const c, next =>
      some ([.let_ next .vec2u (.vec2 (.lit c.toUInt32) (.lit (c >>> 32).toUInt32))], next, next + 1)
  | .u64, .bin op left right, next => do
      let f ← U64Op.wgsl? op
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .vec2u (f vl vr)], n2, n2 + 1)
  | .bool, .ltU left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (lt64 vl vr)], n2, n2 + 1)
  | .f32, .getF32 j, next => (F.scalar j).map fun v => ([], v, next)
  | .f32, .constF32 bits, next =>
      if Wasm.IEEE32.isNaN bits || Wasm.IEEE32.isInfinite bits then none
      else some ([.let_ next .f32 (.toF32 (.lit bits))], next, next + 1)
  | .f32, .binF32 op left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .f32 (.bin (F32Op.wgsl op) (.var vl) (.var vr))], n2, n2 + 1)
  | .f32, .unF32 op operand, next => do
      let (so, vo, n1) ← trExpr F operand next
      pure (so ++ [.let_ n1 .f32 (F32UnOp.wgsl op (.var vo))], n1, n1 + 1)
  | .f32, .ofBits32 operand, next => do
      let (so, vo, n1) ← trExpr F operand next
      pure (so ++ [.let_ n1 .f32 (.toF32 (.fst vo))], n1, n1 + 1)
  | .u64, .toBits32 operand, next => do
      let (so, vo, n1) ← trExpr F operand next
      pure (so ++ [.let_ n1 .vec2u (.vec2 (.toU32 (.var vo)) (.lit 0))], n1, n1 + 1)
  | .u64, .read array position, next => do
      let (b, len) ← F.array array
      let (sp, vp, n1) ← trExpr F position next
      pure (sp ++ [.let_ n1 .vec2u (.vec2 (readAt b vp len 2) (readAt b vp len 3))], n1, n1 + 1)
  | _, _, _ => none

/-- The WGSL value of an IR value of type `type`. -/
def wgslValue : (type : Project.IR.ScalarType) → type.denote → Value
  | .u64, v => pairOf v
  | .f32, bits => .f32 bits
  | .bool, b => .bool b
  | .f64, bits => pairOf bits

/-- The environment and buffers hold the IR locals and arrays as the layout says. -/
structure Layout.Agrees (F : Layout) (locals : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (ctx : Context) (env : Env) : Prop where
  word : ∀ j v, locals j = some (.i64 v) →
    ∃ w m, F.scalar j = some w ∧ env.find w = some (pairOf v, m)
  float : ∀ j b, locals j = some (.f32 b) →
    ∃ w m, F.scalar j = some w ∧ env.find w = some (.f32 b, m)
  array : ∀ a xs, arrays a = some xs → xs.size < 2 ^ 29 ∧ ∃ b len, F.array a = some (b, len) ∧
    ctx.inputs[b]? = some (arrayWords xs) ∧ env.find len = some (.vec2 (UInt32.ofNat xs.size) 0, false)

theorem Env.find_append_fresh (added env : Env) (w : Nat) (h : ∀ b ∈ added, b.1 ≠ w) :
    Env.find (added ++ env) w = Env.find env w := by
  simp only [Env.find, List.find?_append]
  rw [List.find?_eq_none.mpr (by intro b hb; simpa using h b hb)]
  rfl

theorem Layout.Agrees.extend {F : Layout} {locals : Nat → Option Wasm.Value}
    {arrays : Nat → Option (Array UInt64)} {ctx : Context} {env : Env} (added : Env)
    (h : F.Agrees locals arrays ctx env) (hfresh : ∀ b ∈ added, Env.find env b.1 = none) :
    F.Agrees locals arrays ctx (added ++ env) := by
  have keep : ∀ w x, Env.find env w = some x → Env.find (added ++ env) w = some x :=
    fun w x hw => by
      rw [Env.find_append_fresh added env w (fun b hb hbw => by
        have := hfresh b hb; rw [hbw, hw] at this; cases this)]
      exact hw
  refine ⟨fun j v hj => ?_, fun j b hj => ?_, fun a xs ha => ?_⟩
  · obtain ⟨w, m, hw, hf⟩ := h.word j v hj
    exact ⟨w, m, hw, keep _ _ hf⟩
  · obtain ⟨w, m, hw, hf⟩ := h.float j b hj
    exact ⟨w, m, hw, keep _ _ hf⟩
  · obtain ⟨hs, b, len, hF, hb, hl⟩ := h.array a xs ha
    exact ⟨hs, b, len, hF, hb, keep _ _ hl⟩

theorem execList_append (ctx : Context) (run : Run) (a b : List Stmt) :
    Stmt.execList ctx run (a ++ b) = (Stmt.execList ctx run a).bind fun r => Stmt.execList ctx r b := by
  induction a generalizing run with
  | nil => simp [Stmt.execList]
  | cons s rest ih =>
      simp only [List.cons_append, Stmt.execList]
      split
      · rename_i h
        simp only [Option.bind_some]
        induction b generalizing run with
        | nil => simp [Stmt.execList]
        | cons s' rest' _ => simp [Stmt.execList, h]
      · simp only [Option.bind_eq_bind]
        cases Stmt.exec ctx run s with
        | none => rfl
        | some r => simp [ih r]

theorem exec_let (ctx : Context) (env : Env) (writes : List (Nat × UInt32)) (n : Nat) (ty : Ty)
    (e : Expr) (v : Value) (hv : e.eval ctx env = some v) (hty : ty.holds v = true)
    (hfree : Env.find env n = none) :
    Stmt.execList ctx ⟨env, writes, false⟩ [.let_ n ty e] =
      some ⟨(n, v, false) :: env, writes, false⟩ := by
  simp [Stmt.execList, Stmt.exec, hv, hty, hfree]

theorem Env.find_cons_self (env : Env) (n : Nat) (v : Value) (m : Bool) :
    Env.find ((n, v, m) :: env) n = some (v, m) := by
  simp [Env.find]

theorem Env.find_cons_ne (env : Env) (x m : Nat) (v : Value) (mu : Bool) (h : x ≠ m) :
    Env.find ((x, v, mu) :: env) m = Env.find env m := by
  simp [Env.find, List.find?_cons, h]

/-- What running a translation leaves: new bindings with names from `next` up to `next'`, and the
result variable holding the value. -/
def Simulates (ctx : Context) (env : Env) (writes : List (Nat × UInt32)) (stmts : List Stmt)
    (res next next' : Nat) (value : Value) : Prop :=
  ∃ added : Env, Stmt.execList ctx ⟨env, writes, false⟩ stmts =
      some ⟨added ++ env, writes, false⟩ ∧
    (∀ b ∈ added, next ≤ b.1 ∧ b.1 < next') ∧ next ≤ next' ∧ res < next' ∧
    ∃ m, Env.find (added ++ env) res = some (value, m)

theorem find_lt {env : Env} {next w : Nat} {x : Value × Bool} (hFresh : ∀ n, next ≤ n → Env.find env n = none)
    (h : Env.find env w = some x) : w < next := by
  by_contra hw
  rw [hFresh w (by omega)] at h
  cases h

/-- A one-child step: the child's statements, then a `let` of `e` at the child's next variable. -/
theorem simulates_step {ctx : Context} {env : Env} {writes : List (Nat × UInt32)}
    {so : List Stmt} {vo next n1 : Nat} {vChild : Value} (ty : Ty) (e : Expr) (v : Value)
    (hChild : Simulates ctx env writes so vo next n1 vChild)
    (hFresh : ∀ n, next ≤ n → Env.find env n = none)
    (hEval : ∀ added : Env,
      Stmt.execList ctx ⟨env, writes, false⟩ so = some ⟨added ++ env, writes, false⟩ →
      ∀ m, Env.find (added ++ env) vo = some (vChild, m) → e.eval ctx (added ++ env) = some v)
    (hty : ty.holds v = true) :
    Simulates ctx env writes (so ++ [.let_ n1 ty e]) n1 next (n1 + 1) v := by
  obtain ⟨added, hrun, hb, hle, hlt, m, hfind⟩ := hChild
  have hfree : Env.find (added ++ env) n1 = none := by
    rw [Env.find_append_fresh added env n1 (fun b hb' h => by have := hb b hb'; omega)]
    exact hFresh n1 hle
  refine ⟨(n1, v, false) :: added, ?_, ?_, by omega, by omega, false, Env.find_cons_self _ _ _ _⟩
  · rw [execList_append, hrun, Option.bind_some,
      exec_let ctx _ writes n1 ty e v (hEval added hrun m hfind) hty hfree]
    rfl
  · intro b hb'
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact ⟨hle, by omega⟩
    · have := hb b hb'; omega

theorem fresh_append {env added : Env} {next n1 : Nat}
    (hFresh : ∀ n, next ≤ n → Env.find env n = none) (hb : ∀ b ∈ added, next ≤ b.1 ∧ b.1 < n1)
    (hle : next ≤ n1) : ∀ n, n1 ≤ n → Env.find (added ++ env) n = none := fun n hn => by
  rw [Env.find_append_fresh added env n (fun b hb' h => by have := hb b hb'; omega)]
  exact hFresh n (by omega)

/-- A two-child step: the children's statements, then a `let` of `e`, which reads the children's
variables, at the right child's next variable. -/
theorem simulates_bin {ctx : Context} {env : Env} {writes : List (Nat × UInt32)}
    {sl sr : List Stmt} {vl vr next n1 n2 : Nat} {lv rv : Value} (ty : Ty) (e : Expr) (v : Value)
    (hl : Simulates ctx env writes sl vl next n1 lv)
    (hr : ∀ added : Env, (∀ b ∈ added, next ≤ b.1 ∧ b.1 < n1) → next ≤ n1 →
      Simulates ctx (added ++ env) writes sr vr n1 n2 rv)
    (hFresh : ∀ n, next ≤ n → Env.find env n = none)
    (hEval : ∀ env' ml mr, Env.find env' vl = some (lv, ml) → Env.find env' vr = some (rv, mr) →
      e.eval ctx env' = some v)
    (hty : ty.holds v = true) :
    Simulates ctx env writes (sl ++ sr ++ [.let_ n2 ty e]) n2 next (n2 + 1) v := by
  obtain ⟨added1, hrun1, hb1, hle1, hlt1, ml, hf1⟩ := hl
  obtain ⟨added2, hrun2, hb2, hle2, hlt2, mr, hf2⟩ := hr added1 hb1 hle1
  have hjoint : Stmt.execList ctx ⟨env, writes, false⟩ (sl ++ sr) =
      some ⟨(added2 ++ added1) ++ env, writes, false⟩ := by
    rw [execList_append, hrun1, Option.bind_some, hrun2]; simp
  refine simulates_step ty e v ⟨added2 ++ added1, hjoint, fun b hb => ?_, by omega, hlt2, mr,
    by simpa using hf2⟩ hFresh (fun added hrun m hfr => ?_) hty
  · rcases List.mem_append.mp hb with hb | hb
    · have := hb2 b hb; omega
    · have := hb1 b hb; omega
  · rw [hjoint] at hrun
    simp only [Option.some.injEq, Run.mk.injEq, and_true] at hrun
    have hadd : added = added2 ++ added1 := List.append_cancel_right hrun.symm
    subst hadd
    refine hEval _ ml m ?_ hfr
    rw [List.append_assoc, Env.find_append_fresh added2 _ vl
      (fun b hb h => by have := hb2 b hb; omega)]
    exact hf1

/-- Running the translation of an expression leaves its denotation in the result variable. -/
theorem trExpr_sim (F : Layout) (locals : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (ctx : Context) (writes : List (Nat × UInt32)) :
    ∀ {type : Project.IR.ScalarType} (e : Project.IR.Expr type) (next : Nat) (stmts : List Stmt)
      (res next' : Nat), trExpr F e next = some (stmts, res, next') →
    ∀ v, e.denote locals arrays = some v →
    ∀ env, F.Agrees locals arrays ctx env → (∀ n, next ≤ n → Env.find env n = none) →
    Simulates ctx env writes stmts res next next' (wgslValue type v) := by
  intro type e
  induction e with
  | get j =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.map_eq_some_iff] at htr
      obtain ⟨w, hw, heq⟩ := htr
      cases heq
      have hx : locals j = some (.i64 v) := by
        simp only [Project.IR.Expr.denote] at hden
        split at hden <;> simp_all
      obtain ⟨w', m, hw', hf⟩ := hAgree.word j v hx
      rw [hw] at hw'
      cases hw'
      exact ⟨[], by simp [Stmt.execList], by simp, le_refl _, find_lt hFresh hf, m,
        by simpa [wgslValue] using hf⟩
  | const c =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at htr
      obtain ⟨rfl, rfl, rfl⟩ := htr
      simp only [Project.IR.Expr.denote, Option.some.injEq] at hden
      subst hden
      have hfree := hFresh next (le_refl _)
      refine ⟨[(next, pairOf c, false)], ?_, by simp, by omega, by omega, false,
        Env.find_cons_self _ _ _ _⟩
      rw [exec_let ctx env writes next .vec2u _ (pairOf c) (by simp [Expr.eval, pairOf])
        (by simp [pairOf, Ty.holds]) hfree]
      rfl
  | bin op left right ihl ihr =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hop : U64Op.wgsl? op with
      | none => simp [hop] at htr
      | some f =>
        cases hl : trExpr F left next with
        | none => simp [hop, hl] at htr
        | some rl =>
          obtain ⟨sl, vl, n1⟩ := rl
          cases hr : trExpr F right n1 with
          | none => simp [hop, hl, hr] at htr
          | some rr =>
            obtain ⟨sr, vr, n2⟩ := rr
            simp only [hop, hl, hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
            obtain ⟨rfl, rfl, rfl⟩ := htr
            simp only [Project.IR.Expr.denote] at hden
            have hdiv : ¬(op = .divU ∨ op = .remU) := by
              rintro (rfl | rfl) <;> simp [U64Op.wgsl?] at hop
            simp only [hdiv, ↓reduceIte, Option.bind_eq_bind, Option.pure_def] at hden
            cases hdl : left.denote locals arrays with
            | none => simp [hdl] at hden
            | some lv =>
              cases hdr : right.denote locals arrays with
              | none => simp [hdl, hdr] at hden
              | some rv =>
                simp only [hdl, hdr, Option.bind_some, Option.some.injEq] at hden
                subst hden
                exact simulates_bin .vec2u (f vl vr) (wgslValue .u64 (op.apply lv rv))
                  (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
                  (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
                    (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
                    (fresh_append hFresh hb hle))
                  hFresh
                  (fun env' ml mr h1 h2 => by
                    cases op <;> simp only [U64Op.wgsl?, Option.some.injEq, reduceCtorEq] at hop <;>
                      subst hop
                    · exact add64_word ctx env' vl vr lv rv h1 h2
                    · exact mul64_word ctx env' vl vr lv rv h1 h2)
                  (by simp [wgslValue, pairOf, Ty.holds])
  | ltU left right ihl ihr =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hl : trExpr F left next with
      | none => simp [hl] at htr
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hr : trExpr F right n1 with
        | none => simp [hl, hr] at htr
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl, rfl⟩ := htr
          simp only [Project.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hden
          cases hdl : left.denote locals arrays with
          | none => simp [hdl] at hden
          | some lv =>
            cases hdr : right.denote locals arrays with
            | none => simp [hdl, hdr] at hden
            | some rv =>
              simp only [hdl, hdr, Option.bind_some, Option.some.injEq] at hden
              subst hden
              exact simulates_bin .bool (lt64 vl vr) (wgslValue .bool (decide (lv < rv)))
                (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
                (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
                  (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
                  (fresh_append hFresh hb hle))
                hFresh (fun env' ml mr h1 h2 => lt64_word ctx env' vl vr lv rv h1 h2) rfl
  | getF32 j =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.map_eq_some_iff] at htr
      obtain ⟨w, hw, heq⟩ := htr
      cases heq
      have hx : locals j = some (.f32 v) := by
        simp only [Project.IR.Expr.denote] at hden
        split at hden <;> simp_all
      obtain ⟨w', m, hw', hf⟩ := hAgree.float j v hx
      rw [hw] at hw'
      cases hw'
      exact ⟨[], by simp [Stmt.execList], by simp, le_refl _, find_lt hFresh hf, m,
        by simpa [wgslValue] using hf⟩
  | constF32 bits =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr] at htr
      split at htr
      · cases htr
      · simp only [Option.some.injEq, Prod.mk.injEq] at htr
        obtain ⟨rfl, rfl, rfl⟩ := htr
        simp only [Project.IR.Expr.denote, Option.some.injEq] at hden
        subst hden
        have hfree := hFresh next (le_refl _)
        refine ⟨[(next, .f32 bits, false)], ?_, by simp, by omega, by omega, false,
          Env.find_cons_self _ _ _ _⟩
        rw [exec_let ctx env writes next .f32 _ (.f32 bits) (by simp [Expr.eval]) rfl hfree]
        rfl
  | binF32 op left right ihl ihr =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hl : trExpr F left next with
      | none => simp [hl] at htr
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hr : trExpr F right n1 with
        | none => simp [hl, hr] at htr
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl, rfl⟩ := htr
          simp only [Project.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hden
          cases hdl : left.denote locals arrays with
          | none => simp [hdl] at hden
          | some lv =>
            cases hdr : right.denote locals arrays with
            | none => simp [hdl, hdr] at hden
            | some rv =>
              simp only [hdl, hdr, Option.bind_some, Option.some.injEq] at hden
              subst hden
              exact simulates_bin .f32 (.bin (F32Op.wgsl op) (.var vl) (.var vr))
                (wgslValue .f32 (op.apply lv rv))
                (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
                (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
                  (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
                  (fresh_append hFresh hb hle))
                hFresh
                (fun env' ml mr h1 h2 => by
                  simp only [wgslValue] at h1 h2
                  cases op <;> simp [Expr.eval, h1, h2, F32Op.wgsl, BinOp.apply,
                    Project.IR.F32Op.apply, wgslValue])
                rfl
  | unF32 op operand ih =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases ho : trExpr F operand next with
      | none => simp [ho] at htr
      | some ro =>
        obtain ⟨so, vo, n1⟩ := ro
        simp only [ho, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
        obtain ⟨rfl, rfl, rfl⟩ := htr
        simp only [Project.IR.Expr.denote] at hden
        cases hd : operand.denote locals arrays with
        | none => simp [hd] at hden
        | some w =>
          simp only [hd, Option.map_some, Option.some.injEq] at hden
          subst hden
          exact simulates_step .f32 (F32UnOp.wgsl op (.var vo)) (wgslValue .f32 (op.apply w))
            (ih next so vo n1 ho w hd env hAgree hFresh) hFresh
            (fun added _ _ hfr => by
              simp only [wgslValue] at hfr
              cases op <;> simp [Expr.eval, hfr, F32UnOp.wgsl, Project.IR.F32UnOp.apply,
                wgslValue])
            rfl
  | ofBits32 operand ih =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases ho : trExpr F operand next with
      | none => simp [ho] at htr
      | some ro =>
        obtain ⟨so, vo, n1⟩ := ro
        simp only [ho, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
        obtain ⟨rfl, rfl, rfl⟩ := htr
        simp only [Project.IR.Expr.denote] at hden
        cases hd : operand.denote locals arrays with
        | none => simp [hd] at hden
        | some w =>
          simp only [hd, Option.map_some, Option.some.injEq] at hden
          subst hden
          exact simulates_step .f32 (.toF32 (.fst vo)) (wgslValue .f32 w.toUInt32)
            (ih next so vo n1 ho w hd env hAgree hFresh) hFresh
            (fun added _ _ hfr => by
              simp only [wgslValue, pairOf] at hfr
              simp [Expr.eval, hfr, wgslValue])
            rfl
  | toBits32 operand ih =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases ho : trExpr F operand next with
      | none => simp [ho] at htr
      | some ro =>
        obtain ⟨so, vo, n1⟩ := ro
        simp only [ho, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
        obtain ⟨rfl, rfl, rfl⟩ := htr
        simp only [Project.IR.Expr.denote] at hden
        cases hd : operand.denote locals arrays with
        | none => simp [hd] at hden
        | some w =>
          simp only [hd, Option.map_some, Option.some.injEq] at hden
          subst hden
          have hhigh : (w.toUInt64 >>> 32).toUInt32 = 0 := by
            apply UInt32.toNat_inj.mp
            have := w.toNat_lt
            simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
            omega
          exact simulates_step .vec2u (.vec2 (.toU32 (.var vo)) (.lit 0))
            (wgslValue .u64 w.toUInt64)
            (ih next so vo n1 ho w hd env hAgree hFresh) hFresh
            (fun added _ _ hfr => by
              simp only [wgslValue] at hfr
              simp [Expr.eval, hfr, wgslValue, pairOf, hhigh])
            (by simp [wgslValue, pairOf, Ty.holds])
  | read array position ih =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hF : F.array array with
      | none => simp [hF] at htr
      | some bl =>
        obtain ⟨b, len⟩ := bl
        cases hp : trExpr F position next with
        | none => simp [hF, hp] at htr
        | some rp =>
          obtain ⟨sp, vp, n1⟩ := rp
          simp only [hF, hp, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl, rfl⟩ := htr
          simp only [Project.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hden
          cases ha : arrays array with
          | none => simp [ha] at hden
          | some xs =>
            cases hd : position.denote locals arrays with
            | none => simp [ha, hd] at hden
            | some k =>
              simp only [ha, hd, Option.bind_some, Option.some.injEq] at hden
              subst hden
              obtain ⟨hsize, b', len', hF', hbuf, hlen⟩ := hAgree.array array xs ha
              rw [hF] at hF'
              simp only [Option.some.injEq, Prod.mk.injEq] at hF'
              obtain ⟨rfl, rfl⟩ := hF'
              have hChild := ih next sp vp n1 hp k hd env hAgree hFresh
              obtain ⟨added0, hrun0, hb0, hle0, hlt0, m0, hf0⟩ := hChild
              have hlenLt := find_lt hFresh hlen
              exact simulates_step .vec2u (.vec2 (readAt b vp len 2) (readAt b vp len 3))
                (wgslValue .u64 xs[k.toNat]!)
                ⟨added0, hrun0, hb0, hle0, hlt0, m0, hf0⟩ hFresh
                (fun added hrun _ hfr => by
                  rw [hrun0] at hrun
                  simp only [Option.some.injEq, Run.mk.injEq, and_true] at hrun
                  have hadd : added = added0 := List.append_cancel_right hrun.symm
                  subst hadd
                  have hlen' : Env.find (added ++ env) len =
                      some (.vec2 (UInt32.ofNat xs.size) 0, false) := by
                    rw [Env.find_append_fresh added env len
                      (fun b hb h => by have := hb0 b hb; omega)]
                    exact hlen
                  simp only [wgslValue] at hfr
                  have hlo := readAt_word ctx (added ++ env) b vp len xs hsize k false hbuf hfr hlen'
                  have hhi := readAt_word ctx (added ++ env) b vp len xs hsize k true hbuf hfr hlen'
                  simp only [Bool.false_eq_true, ite_false, ite_true] at hlo hhi
                  simp [Expr.eval, hlo, hhi, wgslValue, pairOf, wordHalf])
                (by simp [wgslValue, pairOf, Ty.holds])
  | _ =>
      intro next stmts res next' htr
      simp [trExpr] at htr

end Project.WGSL
