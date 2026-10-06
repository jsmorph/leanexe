import Verified.Compile
import LeanExe.TalosCompat

/-! The compiler's correctness theorem: for every function whose body reads only variables in scope,
the compiled module returns the function's value, without a trap, and leaves the store
unchanged. -/

namespace Verified

open Wasm LeanExe.Pipeline

/-- `after` agrees with `before` on the parameters, the number of locals, and every local below
`base`: the code of an expression with scratch from `base` on changes nothing else. -/
structure Frame (base : Nat) (before after : Locals) : Prop where
  params : after.params = before.params
  length : after.locals.length = before.locals.length
  below : ∀ j < base, after.get j = before.get j

theorem Frame.refl (base : Nat) (s : Locals) : Frame base s s := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {base : Nat} {s1 s2 s3 : Locals} (h1 : Frame base s1 s2)
    (h2 : Frame base s2 s3) : Frame base s1 s3 :=
  ⟨h2.params.trans h1.params, h2.length.trans h1.length,
    fun j hj => (h2.below j hj).trans (h1.below j hj)⟩

/-- The operand stack plays no part in a frame. -/
theorem Frame.values {base : Nat} {s s' : Locals} {values : List Value}
    (h : Frame base { s with values } s') : Frame base s s' :=
  ⟨h.params, h.length, h.below⟩

/-- Local `i`, past the parameters, after a store of `v`. -/
def setLocal (s : Locals) (i : Nat) (v : Value) : Locals :=
  { s with locals := s.locals.set (i - s.params.length) v }

theorem Locals.set?_local {s : Locals} {i : Nat} (v : Value) (hLow : s.params.length ≤ i)
    (hHigh : i < s.params.length + s.locals.length) :
    s.set? i v = some (setLocal s i v) := by
  simp [Locals.set?, setLocal, Nat.not_lt.mpr hLow, hHigh]

theorem Locals.get_setLocal_same {s : Locals} {i : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length) :
    (setLocal s i v).get i = some v := by
  simp [Locals.get, setLocal, Nat.not_lt.mpr hLow, hHigh,
    List.getElem?_set_self (show i - s.params.length < s.locals.length by omega)]

theorem Locals.get_setLocal_ne {s : Locals} {i j : Nat} {v : Value}
    (hLow : s.params.length ≤ i) (hne : j ≠ i) : (setLocal s i v).get j = s.get j := by
  simp only [Locals.get, setLocal, List.length_set]
  split
  · rfl
  · split
    · rw [List.getElem?_set_ne (by omega)]
    · rfl

/-- A store of `v` to local `i`, past the parameters. -/
theorem wp_localSet_local {m : Module} {rest : Program} {Q : Assertion α} {store : Store α}
    {env : HostEnv α} {s : Locals} {i : Nat} {v : Value} {vs : List Value}
    (hLow : s.params.length ≤ i) (hHigh : i < s.params.length + s.locals.length)
    (h : wp m rest Q store (setLocal { s with values := vs } i v) env) :
    wp m (.localSet i :: rest) Q store { s with values := v :: vs } env := by
  rw [wp_localSet_cons]
  simp only
  rw [Locals.set?_local (s := { s with values := v :: vs }) v hLow hHigh]
  exact h

/-- Each variable `x` of the context is in local `locs.getD x.index 0`, below `base`, and that
local holds the word of the variable's value. -/
def Holds {Γ : List Ty} (env : Env Γ) (locs : List Nat) (base : Nat) (s : Locals) : Prop :=
  ∀ (t : Ty) (x : Var Γ t), locs.getD x.index 0 < base ∧
    s.get (locs.getD x.index 0) = some (.i64 (t.encode (env.get x)))

theorem Holds.mono {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base base' : Nat}
    {s : Locals} (h : Holds env locs base s) (hb : base ≤ base') : Holds env locs base' s :=
  fun _ x => ⟨by have := (h _ x).1; omega, (h _ x).2⟩

theorem Holds.frame {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base base' : Nat}
    {s s' : Locals} (h : Holds env locs base s) (hf : Frame base' s s') (hb : base ≤ base') :
    Holds env locs base s' :=
  fun _ x => ⟨(h _ x).1, by rw [hf.below _ (by have := (h _ x).1; omega)]; exact (h _ x).2⟩

theorem Holds.setLocal {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base i : Nat}
    {s : Locals} {v : Value} (h : Holds env locs base s) (hi : base ≤ i)
    (hLow : s.params.length ≤ i) : Holds env locs base (setLocal s i v) :=
  fun _ x => ⟨(h _ x).1, by
    rw [Locals.get_setLocal_ne hLow (by have := (h _ x).1; omega)]; exact (h _ x).2⟩

/-- A `letE` adds its value, in local `base`, as variable 0. -/
theorem Holds.push {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base : Nat} {s : Locals}
    {t : Ty} {v : t.denote} (h : Holds env locs base s)
    (hv : s.get base = some (.i64 (t.encode v))) :
    Holds (Env.cons v env) (base :: locs) (base + 1) s := by
  intro t' x
  cases x with
  | here => exact ⟨by simp [Var.index], by simpa [Var.index, Env.get] using hv⟩
  | there y =>
    simp only [Var.index, Env.get, List.getD_cons_succ]
    exact ⟨by have := (h _ y).1; omega, (h _ y).2⟩

theorem Ty.encode_and (x y : Bool) :
    Ty.encode .bool x &&& Ty.encode .bool y = Ty.encode .bool (x && y) := by
  cases x <;> cases y <;> decide

theorem Ty.encode_or (x y : Bool) :
    Ty.encode .bool x ||| Ty.encode .bool y = Ty.encode .bool (x || y) := by
  cases x <;> cases y <;> decide

theorem Ty.encode_not (x : Bool) :
    UInt64.ofNat ((if Ty.encode .bool x = 0 then (1 : UInt32) else 0).toNat) =
      Ty.encode .bool (!x) := by
  cases x <;> decide

/-- The code of an expression pushes the word of the expression's value from any frame in which
every variable is in its local below `base` and the locals from `base` on are free.  It changes
no parameter and no local below `base`. -/
theorem Expr.code_spec {Γ : List Ty} {t : Ty} (expr : Expr Γ t) (env : Env Γ) (locs : List Nat)
    (base : Nat) (m : Module) (host : HostEnv α) (store : Store α) (s : Locals)
    (hVars : Holds env locs base s) (hBase : s.params.length ≤ base)
    (hRoom : base + expr.width ≤ s.params.length + s.locals.length) (rest : Program)
    (Q : Assertion α)
    (hNext : ∀ s', Frame base s s' →
      wp m rest Q store { s' with values := .i64 (t.encode (expr.denote env)) :: s.values } host) :
    wp m (expr.code locs base ++ rest) Q store s host := by
  induction expr generalizing locs base s rest Q with
  | word value =>
      simpa [Expr.code, Expr.denote, Ty.encode] using hNext s (Frame.refl base s)
  | bool value =>
      simpa [Expr.code, Expr.denote] using hNext s (Frame.refl base s)
  | var x =>
      simp only [Expr.code, List.cons_append, List.nil_append, wp_localGet_cons, (hVars _ x).2]
      simpa [Expr.denote] using hNext s (Frame.refl base s)
  | bin op left right leftSpec rightSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
      have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
      cases op
      case div | rem =>
        simp only [BinOp.scratch] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, List.append_assoc, List.cons_append,
          List.nil_append]
        refine leftSpec env locs (base + 2) s (hVars.mono (by omega)) (by omega) (by omega) _ _
          fun s1 h1 => ?_
        have hp1 : s1.params = s.params := h1.params
        have hl1 : s1.locals.length = s.locals.length := h1.length
        refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
        let s1a := setLocal { s1 with values := s.values } base (.i64 (left.denote env))
        have hp1a : s1a.params = s.params := hp1
        have hl1a : s1a.locals.length = s.locals.length := by simp [s1a, setLocal, hl1]
        have hVars1a : Holds env locs (base + 2) s1a :=
          ((hVars.frame h1 (by omega)).setLocal (le_refl _)
            (by show s1.params.length ≤ base; rw [hp1]; exact hBase)).mono (by omega)
        refine rightSpec env locs (base + 2) s1a hVars1a (by rw [hp1a]; omega)
          (by rw [hp1a, hl1a]; omega) _ _ fun s2 h2 => ?_
        have hp2 : s2.params = s.params := h2.params.trans hp1a
        have hl2 : s2.locals.length = s.locals.length := h2.length.trans hl1a
        refine wp_localSet_local (by rw [hp2]; omega) (by rw [hp2, hl2]; omega) ?_
        let s2b := setLocal { s2 with values := s.values } (base + 1) (.i64 (right.denote env))
        show wp m _ Q store s2b host
        have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote env)) :=
          Locals.get_setLocal_same (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
            (by show base + 1 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega)
        have hLeftSlot : s2b.get base = some (.i64 (left.denote env)) := by
          calc s2b.get base = s2.get base :=
                Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
                  (by omega)
            _ = s1a.get base := h2.below base (by omega)
            _ = some (.i64 (left.denote env)) :=
              Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
                (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
        have hFrame : Frame base s s2b := by
          refine ⟨hp2, by simp [s2b, setLocal, hl2], fun j hj => ?_⟩
          calc s2b.get j = s2.get j :=
                Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
                  (by omega)
            _ = s1a.get j := h2.below j (by omega)
            _ = s1.get j :=
                Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega)
                  (by omega)
            _ = s.get j := h1.below j (by omega)
        have hs2b : s2b.values = s.values := rfl
        simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
        rw [wp_iff_control_types]
        refine wp_iff_cons rfl ?_
        by_cases hZero : right.denote env = 0
        · simp only [hZero, ite_true, ne_eq]
          simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b, Ty.encode] using
            hNext s2b hFrame
        · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
          simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b,
            Ty.encode] using hNext s2b hFrame
      all_goals
        simp only [BinOp.scratch, Nat.zero_add] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, Nat.add_zero, List.append_assoc]
        refine leftSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
        have hp1 : s1.params = s.params := h1.params
        have hl1 : s1.locals.length = s.locals.length := h1.length
        refine rightSpec env locs base
          { s1 with values := .i64 (Ty.encode .word (left.denote env)) :: s.values }
          (hVars.frame h1 le_rfl : Holds env locs base s1)
          (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
          (by show base + right.width ≤ s1.params.length + s1.locals.length
              rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
        have hFrame : Frame base s s2 := h1.trans h2.values
        simpa [Expr.denote, BinOp.apply, Ty.encode, ← UInt64.shiftLeft_eq_shiftLeft_mod,
          ← UInt64.shiftRight_eq_shiftRight_mod] using hNext s2 hFrame
  | cmp op left right leftSpec rightSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
      have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine leftSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine rightSpec env locs base
        { s1 with values := .i64 (Ty.encode .word (left.denote env)) :: s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + right.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      have hFrame : Frame base s s2 := h1.trans h2.values
      have hv := hNext s2 hFrame
      cases op <;>
        simp only [CmpOp.instr, wp_eqI64_cons, wp_neI64_cons, wp_ltUI64_cons, wp_leUI64_cons,
          wp_extendUI32_cons]
      · by_cases hab : left.denote env = right.denote env <;>
          simpa [hab, Expr.denote, CmpOp.apply, Ty.encode] using hv
      · by_cases hab : left.denote env = right.denote env <;>
          simpa [hab, Expr.denote, CmpOp.apply, Ty.encode] using hv
      · by_cases hab : left.denote env < right.denote env <;>
          simpa [hab, Expr.denote, CmpOp.apply, Ty.encode] using hv
      · by_cases hab : left.denote env ≤ right.denote env <;>
          simpa [hab, Expr.denote, CmpOp.apply, Ty.encode] using hv
  | not e eSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine eSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      simp only [wp_eqzI64_cons, wp_extendUI32_cons, Ty.encode_not]
      simpa [Expr.denote] using hNext s1 h1
  | and left right leftSpec rightSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
      have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine leftSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine rightSpec env locs base
        { s1 with values := .i64 (Ty.encode .bool (left.denote env)) :: s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + right.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      simp only [wp_andI64_cons, Ty.encode_and]
      simpa [Expr.denote] using hNext s2 (h1.trans h2.values)
  | or left right leftSpec rightSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
      have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine leftSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine rightSpec env locs base
        { s1 with values := .i64 (Ty.encode .bool (left.denote env)) :: s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + right.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      simp only [wp_orI64_cons, Ty.encode_or]
      simpa [Expr.denote] using hNext s2 (h1.trans h2.values)
  | ite c thenE elseE cSpec thenSpec elseSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hc : c.width ≤ max c.width (max thenE.width elseE.width) := Nat.le_max_left ..
      have ht : thenE.width ≤ max c.width (max thenE.width elseE.width) :=
        (Nat.le_max_left ..).trans (Nat.le_max_right ..)
      have he : elseE.width ≤ max c.width (max thenE.width elseE.width) :=
        (Nat.le_max_right ..).trans (Nat.le_max_right ..)
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine cSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      simp only [wp_eqzI64_cons]
      rw [wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      have hVars1 : Holds env locs base { s1 with values := s.values } :=
        (hVars.frame h1 le_rfl : Holds env locs base s1)
      have hBase1 : ({ s1 with values := s.values } : Locals).params.length ≤ base := by
        show s1.params.length ≤ base; rw [hp1]; exact hBase
      cases hcv : c.denote env
      · simp only [Ty.encode, Bool.cond_false, ite_true, ne_eq]
        rw [← List.append_nil (elseE.code locs base)]
        refine elseSpec env locs base _ hVars1 hBase1
          (by show base + elseE.width ≤ s1.params.length + s1.locals.length
              rw [hp1, hl1]; omega) [] _ fun s2 h2 => ?_
        simpa [Expr.denote, hcv] using hNext s2 (h1.trans h2.values)
      · simp only [Ty.encode, Bool.cond_true, ne_eq]
        rw [← List.append_nil (thenE.code locs base)]
        refine thenSpec env locs base _ hVars1 hBase1
          (by show base + thenE.width ≤ s1.params.length + s1.locals.length
              rw [hp1, hl1]; omega) [] _ fun s2 h2 => ?_
        simpa [Expr.denote, hcv] using hNext s2 (h1.trans h2.values)
  | letE value body valueSpec bodySpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
      have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine valueSpec env locs (base + 1) s (hVars.mono (by omega)) (by omega) (by omega) _ _
        fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
      let s1a := setLocal { s1 with values := s.values } base
        (.i64 (Ty.encode _ (value.denote env)))
      show wp m _ Q store s1a host
      have hp1a : s1a.params = s.params := hp1
      have hl1a : s1a.locals.length = s.locals.length := by simp [s1a, setLocal, hl1]
      have hSlot : s1a.get base = some (.i64 (Ty.encode _ (value.denote env))) :=
        Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
          (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
      have hVars1a : Holds (Env.cons (value.denote env) env) (base :: locs) (base + 1) s1a :=
        ((hVars.frame h1 (by omega)).setLocal (le_refl _)
          (by show s1.params.length ≤ base; rw [hp1]; exact hBase)).push hSlot
      refine bodySpec (Env.cons (value.denote env) env) (base :: locs) (base + 1) s1a hVars1a
        (by rw [hp1a]; omega) (by rw [hp1a, hl1a]; omega) _ _ fun s2 h2 => ?_
      have hFrame : Frame base s s2 := by
        refine ⟨h2.params.trans hp1a, h2.length.trans hl1a, fun j hj => ?_⟩
        calc s2.get j = s1a.get j := h2.below j (by omega)
          _ = s1.get j :=
              Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega)
                (by omega)
          _ = s.get j := h1.below j (by omega)
      have hs1a : s1a.values = s.values := rfl
      simpa [Expr.denote, hs1a] using hNext s2 hFrame

theorem Var.index_lt {Γ : List Ty} {t : Ty} (x : Var Γ t) : x.index < Γ.length := by
  induction x with
  | here => simp [Var.index]
  | there y ih => simp [Var.index]; omega

theorem Env.words_get {Γ : List Ty} {t : Ty} (env : Env Γ) (x : Var Γ t) :
    env.words[x.index]? = some (t.encode (env.get x)) := by
  induction x with
  | here => cases env with | cons v rest => simp [Env.words, Env.get, Var.index]
  | there y ih => cases env with | cons v rest => simp [Env.words, Env.get, Var.index, ih]

theorem Env.words_length {Γ : List Ty} (env : Env Γ) : env.words.length = Γ.length := by
  induction env with
  | nil => rfl
  | cons v rest ih => simp [Env.words, ih]

/-- The correctness theorem.  Function `2 + i` of the compiled module returns
`func.denote args`, without a trap, from any store, and leaves the store unchanged. -/
theorem Func.correct (funcs : List (Func × String)) (i : Nat) (func : Func) (name : String)
    (hFunc : funcs[i]? = some (func, name)) :
    ImplementsPureA false (compile funcs) (2 + i) func.denote := by
  intro host store args
  have hLength : (Scalar.values args).length = func.params.length := by
    simp [Scalar.values, Env.words_length]
  have hNoImports : (compile funcs).imports = [] := rfl
  apply Runs.of_wp_entry_for (f := func.function (2 + i))
    (by rw [hNoImports, List.length_nil, Nat.sub_zero]; exact compile_funcs hFunc)
  have hTake : ((Scalar.values args).reverse.take (func.function (2 + i)).numParams).reverse =
      Scalar.values args := by
    rw [List.take_of_length_le (by simp [Func.function, Func.type, Function.numParams, hLength])]
    simp
  rw [hTake, show (func.function (2 + i)).body =
    func.body.code (List.range func.params.length) func.params.length ++ [] by
      simp [Func.function]]
  refine Expr.code_spec func.body args (List.range func.params.length) func.params.length _ host
    store _ (fun _ x => ?_) (by simp [Function.toLocals, hLength])
    (by simp [Function.toLocals, Func.function, hLength]) [] _ fun s' _ => ?_
  · have hx := x.index_lt
    have hw := args.words_get x
    refine ⟨by simp [List.getD_eq_getElem?_getD, hx], ?_⟩
    simp only [Locals.get, Function.toLocals, Scalar.values, List.length_map, Env.words_length,
      hx, ite_true, List.getD_eq_getElem?_getD, List.getElem?_range, Option.getD_some,
      List.getElem?_map, hw, Option.map_some]
  · simp [Func.function, Func.type, Function.numParams, Func.denote, Scalar.values,
      Env.words_length]

/-- A function's theorem holds for any argument type whose values are those of the function's
arguments. -/
theorem ImplementsPureA.comap [Scalar α] [Scalar β] [Scalar γ] {aborts : Bool} {m : Module}
    {entry : Nat} {f : α → γ} (h : ImplementsPureA aborts m entry f) (g : β → α)
    (hValues : ∀ y, Scalar.values (g y) = Scalar.values y) :
    ImplementsPureA aborts m entry (f ∘ g) := by
  intro env store y
  have := h env store (g y)
  rwa [hValues] at this

end Verified
