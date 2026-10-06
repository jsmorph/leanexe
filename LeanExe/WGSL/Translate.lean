import LeanExe.WGSL.Pair
import LeanExe.IR.Denote

/-!
The translation of IR expressions of the kernel subset into WGSL `let` statements, one per node,
and its simulation lemma: from an environment that holds the IR locals and arrays the way a
`Layout` says, the statements run without error and leave the expression's denotation in the
result variable, a `u64` as the pair of its halves and a binary32 value as an `f32`.
-/

namespace LeanExe.WGSL

/-- Where the translation finds each IR local: a scalar local's WGSL variable, and an array
pointer's buffer and the variable that holds the array's length as a pair.  The locals that
statements assign have types, and their variables are `var`s. -/
structure Layout where
  scalar : Nat → Option Nat
  array : Nat → Option (Nat × Nat)
  assigned : Nat → Option LeanExe.IR.ScalarType := fun _ => none

def F32Op.wgsl : LeanExe.IR.F32Op → BinOp
  | .add => .add
  | .sub => .sub
  | .mul => .mul
  | .div => .div

def F32UnOp.wgsl : LeanExe.IR.F32UnOp → Expr → Expr
  | .sqrt, e => .sqrt e
  | .nearest, e => .round e
  | .abs, e => .abs e

/-- The exponent `s` of a constant `2^s` with `1 ≤ s ≤ 31`. -/
def pow2Exp? (c : UInt64) : Option Nat :=
  (List.range 32).find? fun s => decide (1 ≤ s ∧ c.toNat = 2 ^ s)

theorem pow2Exp?_spec {c : UInt64} {s : Nat} (h : pow2Exp? c = some s) :
    (1 ≤ s ∧ s ≤ 31) ∧ c = UInt64.ofNat (2 ^ s) := by
  unfold pow2Exp? at h
  have hmem := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [List.mem_range, decide_eq_true_eq] at hmem hp
  refine ⟨⟨hp.1, by omega⟩, ?_⟩
  apply UInt64.toNat_inj.mp
  rw [hp.2, UInt64.toNat_ofNat']
  exact (Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))).symm

/-- The pair operation of a `u64` operation with right operand `right`, for those the
translation covers: addition, subtraction, multiplication, and division and remainder by a
constant power of two from 2 to 2^31. -/
def U64Op.wgsl? : LeanExe.IR.U64Op → LeanExe.IR.Expr .u64 → Option (Nat → Nat → Expr)
  | .add, _ => some add64
  | .sub, _ => some sub64
  | .mul, _ => some mul64
  | .divU, .const c => (pow2Exp? c).map fun s a _ => divPow2 a s
  | .remU, .const c => (pow2Exp? c).map fun s a _ => remPow2 a s
  | _, _ => none

/-- The statements that compute an IR expression from variable `next` on, the variable that holds
its value, and the next free variable; `none` outside the kernel subset. -/
def trExpr (F : Layout) : {type : LeanExe.IR.ScalarType} → LeanExe.IR.Expr type → Nat →
    Option (List Stmt × Nat × Nat)
  | .u64, .get j, next => (F.scalar j).map fun v => ([], v, next)
  | .u64, .const c, next =>
      some ([.let_ next .vec2u (.vec2 (.lit c.toUInt32) (.lit (c >>> 32).toUInt32))], next, next + 1)
  | .bool, .bconst b, next => some ([.let_ next .bool (.bool b)], next, next + 1)
  | .u64, .bin op left right, next => do
      let f ← U64Op.wgsl? op right
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .vec2u (f vl vr)], n2, n2 + 1)
  | .bool, .ltU left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (lt64 vl vr)], n2, n2 + 1)
  | .bool, .leU left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (le64 vl vr)], n2, n2 + 1)
  | .bool, .eq left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (eq64 vl vr)], n2, n2 + 1)
  | .bool, .ne left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (.not (eq64 vl vr))], n2, n2 + 1)
  | .bool, .eqF32 left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (.bin .eq (.var vl) (.var vr))], n2, n2 + 1)
  | .bool, .ltF32 left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (.bin .lt (.var vl) (.var vr))], n2, n2 + 1)
  | .bool, .leF32 left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right n1
      pure (sl ++ sr ++ [.let_ n2 .bool (.bin .le (.var vl) (.var vr))], n2, n2 + 1)
  | .bool, .not operand, next => do
      let (so, vo, n1) ← trExpr F operand next
      pure (so ++ [.let_ n1 .bool (.not (.var vo))], n1, n1 + 1)
  | .bool, .and left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right (n1 + 1)
      pure (sl ++ [.var n1 .bool (.bool false),
        .ite (.var vl) (sr ++ [.assign n1 (.var vr)]) []], n1, n2)
  | .bool, .or left right, next => do
      let (sl, vl, n1) ← trExpr F left next
      let (sr, vr, n2) ← trExpr F right (n1 + 1)
      pure (sl ++ [.var n1 .bool (.bool true),
        .ite (.var vl) [] (sr ++ [.assign n1 (.var vr)])], n1, n2)
  | .u64, .ite c t e, next => do
      let (sc, vc, n1) ← trExpr F c next
      let (st, vt, n2) ← trExpr F t (n1 + 1)
      let (se, ve, n3) ← trExpr F e n2
      pure (sc ++ [.var n1 .vec2u (.vec2 (.lit 0) (.lit 0)),
        .ite (.var vc) (st ++ [.assign n1 (.var vt)]) (se ++ [.assign n1 (.var ve)])], n1, n3)
  | .f32, .iteF32 c t e, next => do
      let (sc, vc, n1) ← trExpr F c next
      let (st, vt, n2) ← trExpr F t (n1 + 1)
      let (se, ve, n3) ← trExpr F e n2
      pure (sc ++ [.var n1 .f32 (.toF32 (.lit 0)),
        .ite (.var vc) (st ++ [.assign n1 (.var vt)]) (se ++ [.assign n1 (.var ve)])], n1, n3)
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
def wgslValue : (type : LeanExe.IR.ScalarType) → type.denote → Value
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

/-- The names of an environment that is free from `n` up are below `n`. -/
theorem names_lt {env : Env} {n : Nat} (h : ∀ k, n ≤ k → env.find k = none) :
    ∀ b ∈ env, b.1 < n := by
  intro b hb
  by_contra hlt
  have := h b.1 (by omega)
  simp only [Env.find, Option.map_eq_none_iff, List.find?_eq_none] at this
  exact this b hb (by simp)

theorem find_none_of_names {env : Env} {n : Nat} (h : ∀ b ∈ env, b.1 < n) :
    ∀ k, n ≤ k → env.find k = none := by
  intro k hk
  simp only [Env.find, Option.map_eq_none_iff, List.find?_eq_none]
  intro b hb
  have := h b hb
  simp only [decide_eq_true_eq]
  omega

theorem trExpr_mono (F : Layout) : ∀ {type : LeanExe.IR.ScalarType} (e : LeanExe.IR.Expr type)
    (next : Nat) (stmts : List Stmt) (res next' : Nat),
    trExpr F e next = some (stmts, res, next') → next ≤ next' := by
  intro type e
  induction e with
  | get j | getF32 j =>
      intro next stmts res next' h
      simp only [trExpr, Option.map_eq_some_iff] at h
      obtain ⟨_, _, h⟩ := h
      cases h; omega
  | const c | bconst c =>
      intro next stmts res next' h
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at h
      omega
  | constF32 bits =>
      intro next stmts res next' h
      simp only [trExpr] at h
      split at h
      · cases h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; omega
  | bin op left right ihl ihr =>
      intro next stmts res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hop : U64Op.wgsl? op right with
      | none => simp [hop] at h
      | some f =>
        cases hl : trExpr F left next with
        | none => simp [hop, hl] at h
        | some rl =>
          obtain ⟨sl, vl, n1⟩ := rl
          cases hr : trExpr F right n1 with
          | none => simp [hop, hl, hr] at h
          | some rr =>
            obtain ⟨sr, vr, n2⟩ := rr
            simp only [hop, hl, hr, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            have := ihl _ _ _ _ hl
            have := ihr _ _ _ _ hr
            omega
  | ltU left right ihl ihr | leU left right ihl ihr | eq left right ihl ihr
  | ne left right ihl ihr | eqF32 left right ihl ihr | ltF32 left right ihl ihr
  | leF32 left right ihl ihr | binF32 _ left right ihl ihr =>
      intro next stmts res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hl : trExpr F left next with
      | none => simp [hl] at h
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hr : trExpr F right n1 with
        | none => simp [hl, hr] at h
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hr, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          have := ihl _ _ _ _ hl
          have := ihr _ _ _ _ hr
          omega
  | not operand ih | unF32 _ operand ih | ofBits32 operand ih | toBits32 operand ih =>
      intro next stmts res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases ho : trExpr F operand next with
      | none => simp [ho] at h
      | some ro =>
        obtain ⟨so, vo, n1⟩ := ro
        simp only [ho, Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        have := ih _ _ _ _ ho
        omega
  | and left right ihl ihr | or left right ihl ihr =>
      intro next stmts res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hl : trExpr F left next with
      | none => simp [hl] at h
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hr : trExpr F right (n1 + 1) with
        | none => simp [hl, hr] at h
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hr, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          have := ihl _ _ _ _ hl
          have := ihr _ _ _ _ hr
          omega
  | ite c t e ihc iht ihe | iteF32 c t e ihc iht ihe =>
      intro next stmts res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hc : trExpr F c next with
      | none => simp [hc] at h
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ht : trExpr F t (n1 + 1) with
        | none => simp [hc, ht] at h
        | some rt =>
          obtain ⟨st, vt, n2⟩ := rt
          cases he : trExpr F e n2 with
          | none => simp [hc, ht, he] at h
          | some re =>
            obtain ⟨se, ve, n3⟩ := re
            simp only [hc, ht, he, Option.bind_some, Option.pure_def, Option.some.injEq,
              Prod.mk.injEq] at h
            have := ihc _ _ _ _ hc
            have := iht _ _ _ _ ht
            have := ihe _ _ _ _ he
            omega
  | read array position ih =>
      intro next stmts res next' h
      simp only [trExpr, Option.bind_eq_bind] at h
      cases hF : F.array array with
      | none => simp [hF] at h
      | some bl =>
        cases hp : trExpr F position next with
        | none => simp [hF, hp] at h
        | some rp =>
          obtain ⟨sp, vp, n1⟩ := rp
          simp only [hF, hp, Option.bind_some, Option.pure_def, Option.some.injEq,
            Prod.mk.injEq] at h
          have := ih _ _ _ _ hp
          omega
  | _ =>
      intro next stmts res next' h
      simp [trExpr] at h

theorem Env.set_fresh (env : Env) (w : Nat) (v : Value) (h : ∀ b ∈ env, b.1 ≠ w) :
    env.set w v = env := by
  induction env with
  | nil => rfl
  | cons x env ih =>
      simp only [Env.set, List.map_cons, List.cons.injEq]
      exact ⟨by simp [h x (by simp)], ih fun b hb => h b (by simp [hb])⟩

theorem Env.set_append (a b : Env) (w : Nat) (v : Value) :
    (a ++ b).set w v = a.set w v ++ b.set w v := by
  simp [Env.set]


theorem U64Op.wgsl?_eval {op : LeanExe.IR.U64Op} {right : LeanExe.IR.Expr .u64}
    {f : Nat → Nat → Expr} (h : U64Op.wgsl? op right = some f)
    {locals : Nat → Option Wasm.Value} {arrays : Nat → Option (Array UInt64)} {rv : UInt64}
    (hr : right.denote locals arrays = some rv) (ctx : Context) (env : Env) {ma mb : Bool}
    (a b : Nat) (lv : UInt64) (ha : env.find a = some (pairOf lv, ma))
    (hb : env.find b = some (pairOf rv, mb)) :
    (f a b).eval ctx env = some (pairOf (op.apply lv rv)) := by
  cases op with
  | add => cases h; exact add64_word ctx env a b lv rv ha hb
  | sub => cases h; exact sub64_word ctx env a b lv rv ha hb
  | mul => cases h; exact mul64_word ctx env a b lv rv ha hb
  | divU =>
      cases right with
      | const c =>
          simp only [U64Op.wgsl?, Option.map_eq_some_iff] at h
          obtain ⟨s, hs, rfl⟩ := h
          obtain ⟨hs1, rfl⟩ := pow2Exp?_spec hs
          simp only [LeanExe.IR.Expr.denote, Option.some.injEq] at hr
          subst hr
          have hne : UInt64.ofNat (2 ^ s) ≠ 0 := fun h0 => by
            have := congrArg UInt64.toNat h0
            rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega)
              (by omega))] at this
            simp at this
          simp only [LeanExe.IR.U64Op.apply, hne, ↓reduceIte]
          exact divPow2_word ctx env a s lv hs1 ha
      | _ => simp [U64Op.wgsl?] at h
  | remU =>
      cases right with
      | const c =>
          simp only [U64Op.wgsl?, Option.map_eq_some_iff] at h
          obtain ⟨s, hs, rfl⟩ := h
          obtain ⟨hs1, rfl⟩ := pow2Exp?_spec hs
          simp only [LeanExe.IR.Expr.denote, Option.some.injEq] at hr
          subst hr
          have hne : UInt64.ofNat (2 ^ s) ≠ 0 := fun h0 => by
            have := congrArg UInt64.toNat h0
            rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (Nat.pow_lt_pow_right (by omega)
              (by omega))] at this
            simp at this
          simp only [LeanExe.IR.U64Op.apply, hne, ↓reduceIte]
          exact remPow2_word ctx env a s lv hs1 ha
      | _ => simp [U64Op.wgsl?] at h
  | _ => simp [U64Op.wgsl?] at h

/-- A branch that computes a value and assigns it to the `var` `n1` declared before the `if`. -/
theorem branch_assign {ctx : Context} {writes : List (Nat × UInt32)} {st : List Stmt}
    {vt lo hi : Nat} {zero v : Value} (n1 : Nat) (rest : Env)
    (h : Simulates ctx ((n1, zero, true) :: rest) writes st vt lo hi v) (hlo : n1 < lo)
    (hsame : zero.sameType v = true) (hn1 : ∀ x ∈ rest, x.1 ≠ n1) :
    ∃ addt, Stmt.execList ctx ⟨(n1, zero, true) :: rest, writes, false⟩
        (st ++ [.assign n1 (.var vt)]) = some ⟨addt ++ (n1, v, true) :: rest, writes, false⟩ ∧
      ∀ x ∈ addt, n1 < x.1 ∧ x.1 < hi := by
  obtain ⟨addt, hrun, hb, hle, hlt, m, hf⟩ := h
  have hfn1 : Env.find (addt ++ (n1, zero, true) :: rest) n1 = some (zero, true) := by
    rw [Env.find_append_fresh _ _ n1 (fun x hx h => by have := hb x hx; omega)]
    exact Env.find_cons_self _ _ _ _
  have hset : (addt ++ (n1, zero, true) :: rest).set n1 v = addt ++ (n1, v, true) :: rest := by
    rw [Env.set_append, Env.set_fresh addt n1 v (fun x hx h => by have := hb x hx; omega)]
    simp only [Env.set, List.map_cons, ↓reduceIte]
    exact congrArg (fun r => addt ++ (n1, v, true) :: r) (Env.set_fresh rest n1 v hn1)
  refine ⟨addt, ?_, fun x hx => ⟨by have := hb x hx; omega, (hb x hx).2⟩⟩
  rw [execList_append, hrun, Option.bind_some]
  simp [Stmt.execList, Stmt.exec, Expr.eval, hf, hfn1, hsame, hset]

/-- A conditional: the condition's statements, a `var` `n1` at the condition's next variable,
and an `if` whose taken branch leaves the value in the `var`. -/
theorem simulates_cond {ctx : Context} {env : Env} {writes : List (Nat × UInt32)}
    {sc ts es : List Stmt} {vc next n1 hi : Nat} {b : Bool} {ty : Ty} {ze : Expr} {zero v : Value}
    (hc : Simulates ctx env writes sc vc next n1 (.bool b))
    (hFresh : ∀ n, next ≤ n → Env.find env n = none)
    (hze : ∀ env', ze.eval ctx env' = some zero) (hzt : ty.holds zero = true) (hhi : n1 < hi)
    (hbr : ∀ added : Env, (∀ x ∈ added, next ≤ x.1 ∧ x.1 < n1) →
      ∃ addt, Stmt.execList ctx ⟨(n1, zero, true) :: (added ++ env), writes, false⟩
          (if b then ts else es) = some ⟨addt ++ (n1, v, true) :: (added ++ env), writes, false⟩ ∧
        ∀ x ∈ addt, n1 < x.1 ∧ x.1 < hi) :
    Simulates ctx env writes (sc ++ [.var n1 ty ze, .ite (.var vc) ts es]) n1 next hi v := by
  obtain ⟨added, hrun, hb, hle, hlt, m, hf⟩ := hc
  have hfree : Env.find (added ++ env) n1 = none := by
    rw [Env.find_append_fresh added env n1 (fun x hx h => by have := hb x hx; omega)]
    exact hFresh n1 hle
  have hfc : Env.find ((n1, zero, true) :: (added ++ env)) vc = some (.bool b, m) := by
    rw [Env.find_cons_ne _ _ _ _ _ (by omega)]
    exact hf
  obtain ⟨addt, hbranch, hbt⟩ := hbr added hb
  have hdrop : List.drop ((addt ++ (n1, v, true) :: (added ++ env)).length -
      ((n1, zero, true) :: (added ++ env)).length) (addt ++ (n1, v, true) :: (added ++ env)) =
      (n1, v, true) :: (added ++ env) := by
    simp only [List.length_append, List.length_cons, Nat.add_sub_cancel]
    exact List.drop_left
  refine ⟨(n1, v, true) :: added, ?_, ?_, by omega, hhi, true, by
    simp only [List.cons_append]; exact Env.find_cons_self _ _ _ _⟩
  · rw [execList_append, hrun, Option.bind_some]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hbranch <;>
      simp [Stmt.execList, Stmt.exec, hze, hzt, hfree, Expr.eval, hfc, hbranch, hdrop]
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨hle, hhi⟩
    · have := hb x hx; omega

/-- Running the translation of an expression leaves its denotation in the result variable. -/
theorem trExpr_sim (F : Layout) (locals : Nat → Option Wasm.Value)
    (arrays : Nat → Option (Array UInt64)) (ctx : Context) (writes : List (Nat × UInt32)) :
    ∀ {type : LeanExe.IR.ScalarType} (e : LeanExe.IR.Expr type) (next : Nat) (stmts : List Stmt)
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
        simp only [LeanExe.IR.Expr.denote] at hden
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
      simp only [LeanExe.IR.Expr.denote, Option.some.injEq] at hden
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
      cases hop : U64Op.wgsl? op right with
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
            simp only [LeanExe.IR.Expr.denote] at hden
            obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
            exact simulates_bin .vec2u (f vl vr) (wgslValue .u64 (op.apply lv rv))
              (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
              (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
                (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
                (fresh_append hFresh hb hle))
              hFresh
              (fun env' ml mr h1 h2 => U64Op.wgsl?_eval hop hdr ctx env' vl vr lv h1 h2)
              (by simp [wgslValue, pairOf, Ty.holds])
  | bconst c =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.some.injEq, Prod.mk.injEq] at htr
      obtain ⟨rfl, rfl, rfl⟩ := htr
      simp only [LeanExe.IR.Expr.denote, Option.some.injEq] at hden
      subst hden
      have hfree := hFresh next (le_refl _)
      refine ⟨[(next, .bool c, false)], ?_, by simp, by omega, by omega, false,
        Env.find_cons_self _ _ _ _⟩
      rw [exec_let ctx env writes next .bool _ (.bool c) (by simp [Expr.eval]) rfl hfree]
      rfl
  | leU left right ihl ihr =>
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
          simp only [LeanExe.IR.Expr.denote] at hden
          obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
          exact simulates_bin .bool (le64 vl vr) (wgslValue .bool (decide (lv ≤ rv)))
            (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
            (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
              (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
              (fresh_append hFresh hb hle))
            hFresh (fun env' ml mr h1 h2 => by exact le64_word ctx env' vl vr lv rv h1 h2) rfl
  | eq left right ihl ihr =>
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
          simp only [LeanExe.IR.Expr.denote] at hden
          obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
          exact simulates_bin .bool (eq64 vl vr) (wgslValue .bool (lv == rv))
            (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
            (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
              (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
              (fresh_append hFresh hb hle))
            hFresh (fun env' ml mr h1 h2 => by exact eq64_word ctx env' vl vr lv rv h1 h2) rfl
  | ne left right ihl ihr =>
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
          simp only [LeanExe.IR.Expr.denote] at hden
          obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
          exact simulates_bin .bool (.not (eq64 vl vr)) (wgslValue .bool (lv != rv))
            (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
            (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
              (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
              (fresh_append hFresh hb hle))
            hFresh (fun env' ml mr h1 h2 => by simp [Expr.eval, eq64_word ctx env' vl vr lv rv h1 h2, bne, wgslValue]) rfl
  | eqF32 left right ihl ihr =>
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
          simp only [LeanExe.IR.Expr.denote] at hden
          obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
          exact simulates_bin .bool (.bin .eq (.var vl) (.var vr)) (wgslValue .bool (Wasm.IEEE32.eq lv rv))
            (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
            (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
              (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
              (fresh_append hFresh hb hle))
            hFresh (fun env' ml mr h1 h2 => by simp only [wgslValue] at h1 h2; simp [Expr.eval, h1, h2, BinOp.apply, wgslValue]) rfl
  | ltF32 left right ihl ihr =>
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
          simp only [LeanExe.IR.Expr.denote] at hden
          obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
          exact simulates_bin .bool (.bin .lt (.var vl) (.var vr)) (wgslValue .bool (Wasm.IEEE32.lt lv rv))
            (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
            (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
              (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
              (fresh_append hFresh hb hle))
            hFresh (fun env' ml mr h1 h2 => by simp only [wgslValue] at h1 h2; simp [Expr.eval, h1, h2, BinOp.apply, wgslValue]) rfl
  | leF32 left right ihl ihr =>
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
          simp only [LeanExe.IR.Expr.denote] at hden
          obtain ⟨lv, rv, hdl, hdr, rfl⟩ := LeanExe.IR.denote_two hden
          exact simulates_bin .bool (.bin .le (.var vl) (.var vr)) (wgslValue .bool (Wasm.IEEE32.le lv rv))
            (ihl next sl vl n1 hl lv hdl env hAgree hFresh)
            (fun added hb hle => ihr n1 sr vr n2 hr rv hdr (added ++ env)
              (hAgree.extend added (fun b hb' => hFresh b.1 (hb b hb').1))
              (fresh_append hFresh hb hle))
            hFresh (fun env' ml mr h1 h2 => by simp only [wgslValue] at h1 h2; simp [Expr.eval, h1, h2, BinOp.apply, wgslValue]) rfl
  | not operand ih =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases ho : trExpr F operand next with
      | none => simp [ho] at htr
      | some ro =>
        obtain ⟨so, vo, n1⟩ := ro
        simp only [ho, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
        obtain ⟨rfl, rfl, rfl⟩ := htr
        simp only [LeanExe.IR.Expr.denote] at hden
        obtain ⟨w, hd, rfl⟩ := Option.map_eq_some_iff.mp hden
        exact simulates_step .bool (.not (.var vo)) (wgslValue .bool (!w))
          (ih next so vo n1 ho w hd env hAgree hFresh) hFresh
          (fun added _ _ hfr => by
            simp only [wgslValue] at hfr
            simp [Expr.eval, hfr, wgslValue])
          rfl
  | and left right ihl ihr | or left right ihl ihr =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hl : trExpr F left next with
      | none => simp [hl] at htr
      | some rl =>
        obtain ⟨sl, vl, n1⟩ := rl
        cases hr : trExpr F right (n1 + 1) with
        | none => simp [hl, hr] at htr
        | some rr =>
          obtain ⟨sr, vr, n2⟩ := rr
          simp only [hl, hr, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
          obtain ⟨rfl, rfl, rfl⟩ := htr
          simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind] at hden
          cases hdl : left.denote locals arrays with
          | none => simp [hdl] at hden
          | some b =>
            simp only [hdl, Option.bind_some] at hden
            have hL := ihl next sl vl n1 hl b hdl env hAgree hFresh
            have hle2 := trExpr_mono F right _ _ _ _ hr
            obtain ⟨_, _, _, hle1, hn1, _⟩ := id hL
            refine simulates_cond hL hFresh (fun _ => rfl) rfl (by omega) fun added hb => ?_
            have hEnvNames : ∀ x ∈ added ++ env, x.1 < n1 := fun x hx => by
              rcases List.mem_append.mp hx with hx | hx
              · exact (hb x hx).2
              · have := names_lt hFresh x hx; omega
            cases b <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.pure_def,
              Option.some.injEq] at hden ⊢
            all_goals first
              | (subst hden
                 exact ⟨[], by simp [Stmt.execList, wgslValue], by simp⟩)
              | (exact branch_assign (v := wgslValue .bool v) n1
                    (added ++ env)
                    (ihr (n1 + 1) sr vr n2 hr v hden _
                      (hAgree.extend ((n1, _, true) :: added) (fun x hx => by
                        rcases List.mem_cons.mp hx with rfl | hx
                        · exact hFresh _ (by omega)
                        · exact hFresh x.1 (hb x hx).1))
                      (find_none_of_names fun x hx => by
                        rcases List.mem_cons.mp hx with rfl | hx
                        · simp
                        · have := hEnvNames x hx; omega))
                    (by omega) (by simp [Value.sameType, wgslValue])
                    (fun x hx h => by have := hEnvNames x hx; omega))
  | ite c t e ihc iht ihe =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hc : trExpr F c next with
      | none => simp [hc] at htr
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ht : trExpr F t (n1 + 1) with
        | none => simp [hc, ht] at htr
        | some rt =>
          obtain ⟨st, vt, n2⟩ := rt
          cases he : trExpr F e n2 with
          | none => simp [hc, ht, he] at htr
          | some re =>
            obtain ⟨se, ve, n3⟩ := re
            simp only [hc, ht, he, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
            obtain ⟨rfl, rfl, rfl⟩ := htr
            simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind] at hden
            cases hdc : c.denote locals arrays with
            | none => simp [hdc] at hden
            | some b =>
              simp only [hdc, Option.bind_some] at hden
              have hC := ihc next sc vc n1 hc b hdc env hAgree hFresh
              have hle2 := trExpr_mono F t _ _ _ _ ht
              have hle3 := trExpr_mono F e _ _ _ _ he
              obtain ⟨_, _, _, hle1, hn1, _⟩ := id hC
              refine simulates_cond hC hFresh (fun _ => rfl) rfl (by omega) fun added hb => ?_
              have hEnvNames : ∀ x ∈ added ++ env, x.1 < n1 := fun x hx => by
                rcases List.mem_append.mp hx with hx | hx
                · exact (hb x hx).2
                · have := names_lt hFresh x hx; omega
              have hAg : F.Agrees locals arrays ctx ((n1, .vec2 0 0, true) :: (added ++ env)) :=
                hAgree.extend ((n1, _, true) :: added) (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact hFresh _ (by omega)
                  · exact hFresh x.1 (hb x hx).1)
              have hFr : ∀ k, n1 + 1 ≤ k →
                  Env.find ((n1, .vec2 0 0, true) :: (added ++ env)) k = none :=
                find_none_of_names fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · simp
                  · have := hEnvNames x hx; omega
              cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hden ⊢
              · obtain ⟨addt, hrun, hbt⟩ := branch_assign (v := wgslValue .u64 v) n1 (added ++ env)
                  (ihe n2 se ve n3 he v hden _ hAg (fun k hk => hFr k (by omega)))
                  (by omega) (by simp [Value.sameType, wgslValue, pairOf])
                  (fun x hx h => by have := hEnvNames x hx; omega)
                exact ⟨addt, hrun, hbt⟩
              · obtain ⟨addt, hrun, hbt⟩ := branch_assign (v := wgslValue .u64 v) n1 (added ++ env)
                  (iht (n1 + 1) st vt n2 ht v hden _ hAg hFr)
                  (by omega) (by simp [Value.sameType, wgslValue, pairOf])
                  (fun x hx h => by have := hEnvNames x hx; omega)
                exact ⟨addt, hrun, fun x hx => ⟨(hbt x hx).1, by have := (hbt x hx).2; omega⟩⟩
  | iteF32 c t e ihc iht ihe =>
      intro next stmts res next' htr v hden env hAgree hFresh
      simp only [trExpr, Option.bind_eq_bind, Option.pure_def] at htr
      cases hc : trExpr F c next with
      | none => simp [hc] at htr
      | some rc =>
        obtain ⟨sc, vc, n1⟩ := rc
        cases ht : trExpr F t (n1 + 1) with
        | none => simp [hc, ht] at htr
        | some rt =>
          obtain ⟨st, vt, n2⟩ := rt
          cases he : trExpr F e n2 with
          | none => simp [hc, ht, he] at htr
          | some re =>
            obtain ⟨se, ve, n3⟩ := re
            simp only [hc, ht, he, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at htr
            obtain ⟨rfl, rfl, rfl⟩ := htr
            simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind] at hden
            cases hdc : c.denote locals arrays with
            | none => simp [hdc] at hden
            | some b =>
              simp only [hdc, Option.bind_some] at hden
              have hC := ihc next sc vc n1 hc b hdc env hAgree hFresh
              have hle2 := trExpr_mono F t _ _ _ _ ht
              have hle3 := trExpr_mono F e _ _ _ _ he
              obtain ⟨_, _, _, hle1, hn1, _⟩ := id hC
              refine simulates_cond hC hFresh (fun _ => rfl) rfl (by omega) fun added hb => ?_
              have hEnvNames : ∀ x ∈ added ++ env, x.1 < n1 := fun x hx => by
                rcases List.mem_append.mp hx with hx | hx
                · exact (hb x hx).2
                · have := names_lt hFresh x hx; omega
              have hAg : F.Agrees locals arrays ctx ((n1, .f32 0, true) :: (added ++ env)) :=
                hAgree.extend ((n1, _, true) :: added) (fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · exact hFresh _ (by omega)
                  · exact hFresh x.1 (hb x hx).1)
              have hFr : ∀ k, n1 + 1 ≤ k →
                  Env.find ((n1, .f32 0, true) :: (added ++ env)) k = none :=
                find_none_of_names fun x hx => by
                  rcases List.mem_cons.mp hx with rfl | hx
                  · simp
                  · have := hEnvNames x hx; omega
              cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at hden ⊢
              · obtain ⟨addt, hrun, hbt⟩ := branch_assign (v := wgslValue .f32 v) n1 (added ++ env)
                  (ihe n2 se ve n3 he v hden _ hAg (fun k hk => hFr k (by omega)))
                  (by omega) (by simp [Value.sameType, wgslValue, pairOf])
                  (fun x hx h => by have := hEnvNames x hx; omega)
                exact ⟨addt, hrun, hbt⟩
              · obtain ⟨addt, hrun, hbt⟩ := branch_assign (v := wgslValue .f32 v) n1 (added ++ env)
                  (iht (n1 + 1) st vt n2 ht v hden _ hAg hFr)
                  (by omega) (by simp [Value.sameType, wgslValue, pairOf])
                  (fun x hx h => by have := hEnvNames x hx; omega)
                exact ⟨addt, hrun, fun x hx => ⟨(hbt x hx).1, by have := (hbt x hx).2; omega⟩⟩
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
          simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hden
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
        simp only [LeanExe.IR.Expr.denote] at hden
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
        simp only [LeanExe.IR.Expr.denote, Option.some.injEq] at hden
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
          simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hden
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
                    LeanExe.IR.F32Op.apply, wgslValue])
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
        simp only [LeanExe.IR.Expr.denote] at hden
        cases hd : operand.denote locals arrays with
        | none => simp [hd] at hden
        | some w =>
          simp only [hd, Option.map_some, Option.some.injEq] at hden
          subst hden
          exact simulates_step .f32 (F32UnOp.wgsl op (.var vo)) (wgslValue .f32 (op.apply w))
            (ih next so vo n1 ho w hd env hAgree hFresh) hFresh
            (fun added _ _ hfr => by
              simp only [wgslValue] at hfr
              cases op <;> simp [Expr.eval, hfr, F32UnOp.wgsl, LeanExe.IR.F32UnOp.apply,
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
        simp only [LeanExe.IR.Expr.denote] at hden
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
        simp only [LeanExe.IR.Expr.denote] at hden
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
          simp only [LeanExe.IR.Expr.denote, Option.bind_eq_bind, Option.pure_def] at hden
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

end LeanExe.WGSL
