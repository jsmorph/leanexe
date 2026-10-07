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

@[simp] theorem Ty.values_word (v : UInt64) : Ty.values .word v = [.i64 v] := rfl

@[simp] theorem Ty.values_bool (b : Bool) : Ty.values .bool b = [.i64 (boolWord b)] := rfl

@[simp] theorem Ty.values_pair {a b : Ty} (p : (Ty.pair a b).denote) :
    Ty.values (.pair a b) p = a.values p.1 ++ b.values p.2 := rfl

theorem rev_values_word (v : UInt64) (vs : List Value) :
    (Ty.values .word v).reverse ++ vs = .i64 v :: vs := rfl

theorem rev_values_bool (b : Bool) (vs : List Value) :
    (Ty.values .bool b).reverse ++ vs = .i64 (boolWord b) :: vs := rfl

theorem Ty.values_length : (t : Ty) → (v : t.denote) → (t.values v).length = t.width
  | .word, _ => rfl
  | .bool, _ => rfl
  | .pair a b, p => by simp [Ty.width, Ty.values_length a, Ty.values_length b]

/-- Locals `loc` to `loc + vals.length - 1` hold `vals`, in order. -/
def LocalsHold (s : Locals) (loc : Nat) (vals : List Value) : Prop :=
  ∀ k (hk : k < vals.length), s.get (loc + k) = some vals[k]

/-- Loading locals that hold `vals` pushes `vals` in order. -/
theorem wp_loadCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    (vals : List Value) {loc w : Nat} {s : Locals} {rest : Program} (hw : vals.length = w)
    (hold : LocalsHold s loc vals)
    (h : wp m rest Q store { s with values := vals.reverse ++ s.values } host) :
    wp m (loadCode loc w ++ rest) Q store s host := by
  induction vals generalizing loc w s with
  | nil => subst hw; simpa [loadCode] using h
  | cons v vs ih =>
    subst hw
    have h0 : s.get loc = some v := by
      have := hold 0 (by simp)
      rw [Nat.add_zero] at this
      exact this
    simp only [loadCode, List.length_cons, List.cons_append, wp_localGet_cons, h0]
    refine ih rfl (fun k hk => ?_) ?_
    · have := hold (k + 1) (by simp; omega)
      rw [show loc + (k + 1) = loc + 1 + k by omega] at this
      simpa [-Locals.get] using this
    · simpa [List.append_assoc] using h

/-- Storing the top words `vals` of the stack in locals from `loc` on leaves them there and
changes no other local. -/
theorem wp_storeCode {m : Module} {Q : Assertion α} {store : Store α} {host : HostEnv α}
    {rest : Program} (vals : List Value) (loc w : Nat) (s : Locals) (vs : List Value)
    (hw : vals.length = w) (hLow : s.params.length ≤ loc)
    (hHigh : loc + w ≤ s.params.length + s.locals.length)
    (hNext : ∀ s', s'.params = s.params → s'.locals.length = s.locals.length →
      LocalsHold s' loc vals → (∀ j, j < loc ∨ loc + w ≤ j → s'.get j = s.get j) →
      wp m rest Q store { s' with values := vs } host) :
    wp m (storeCode loc w ++ rest) Q store { s with values := vals.reverse ++ vs } host := by
  induction vals generalizing loc w s vs rest with
  | nil =>
    subst hw
    exact hNext s rfl rfl (fun k hk => absurd hk (by simp)) fun _ _ => rfl
  | cons v vals ih =>
    subst hw
    simp only [storeCode, List.length_cons, List.append_assoc, List.reverse_cons,
      List.cons_append, List.nil_append]
    refine ih (loc + 1) _ s (v :: vs) rfl (by omega) (by simp at hHigh ⊢; omega)
      fun s1 hp1 hl1 hold1 hout1 => ?_
    refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; simp at hHigh; omega) ?_
    refine hNext (setLocal { s1 with values := vs } loc v) hp1 (by simp [setLocal, hl1])
      (fun k hk => ?_) fun j hj => ?_
    · cases k with
      | zero =>
        simpa [-Locals.get] using Locals.get_setLocal_same (s := { s1 with values := vs }) (v := v)
          (by show s1.params.length ≤ loc; rw [hp1]; omega)
          (by show loc < s1.params.length + s1.locals.length
              rw [hp1, hl1]; simp at hHigh; omega)
      | succ k =>
        rw [Locals.get_setLocal_ne (by show s1.params.length ≤ loc; rw [hp1]; omega) (by omega)]
        have := hold1 k (by simp at hk; omega)
        rw [show loc + 1 + k = loc + (k + 1) by omega] at this
        simpa [-Locals.get] using this
    · rw [Locals.get_setLocal_ne (by show s1.params.length ≤ loc; rw [hp1]; omega)
        (by simp at hj; omega)]
      exact hout1 j (by simp at hj; omega)

/-- Each variable `x` of the context starts at local `locs.getD x.index 0`, its words end below
`base`, and its locals hold the words of its value. -/
def Holds {Γ : List Ty} (env : Env Γ) (locs : List Nat) (base : Nat) (s : Locals) : Prop :=
  ∀ (t : Ty) (x : Var Γ t), locs.getD x.index 0 + t.width ≤ base ∧
    LocalsHold s (locs.getD x.index 0) (t.values (env.get x))

theorem Holds.mono {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base base' : Nat}
    {s : Locals} (h : Holds env locs base s) (hb : base ≤ base') : Holds env locs base' s :=
  fun _ x => ⟨by have := (h _ x).1; omega, (h _ x).2⟩

/-- `Holds` depends only on the locals below `base`. -/
theorem Holds.agree {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base : Nat} {s s' : Locals}
    (h : Holds env locs base s) (hs : ∀ j < base, s'.get j = s.get j) :
    Holds env locs base s' := by
  intro t x
  refine ⟨(h t x).1, fun k hk => ?_⟩
  have hlen := Ty.values_length t (env.get x)
  rw [hs _ (by have := (h t x).1; omega)]
  exact (h t x).2 k hk

theorem Holds.frame {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base base' : Nat}
    {s s' : Locals} (h : Holds env locs base s) (hf : Frame base' s s') (hb : base ≤ base') :
    Holds env locs base s' :=
  h.agree fun j hj => hf.below j (by omega)

theorem Holds.setLocal {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base i : Nat}
    {s : Locals} {v : Value} (h : Holds env locs base s) (hi : base ≤ i)
    (hLow : s.params.length ≤ i) : Holds env locs base (setLocal s i v) :=
  h.agree fun j hj => Locals.get_setLocal_ne hLow (by omega)

/-- A binding adds its value, in the locals from `base` on, as variable 0. -/
theorem Holds.push {Γ : List Ty} {env : Env Γ} {locs : List Nat} {base : Nat} {s : Locals}
    {t : Ty} {v : t.denote} (h : Holds env locs base s) (hv : LocalsHold s base (t.values v)) :
    Holds (Env.cons v env) (base :: locs) (base + t.width) s := by
  intro t' x
  cases x with
  | here => exact ⟨by simp [Var.index], by simpa [Var.index, Env.get] using hv⟩
  | there y =>
    simp only [Var.index, Env.get, List.getD_cons_succ]
    exact ⟨by have := (h _ y).1; omega, (h _ y).2⟩

theorem boolWord_and (x y : Bool) : boolWord x &&& boolWord y = boolWord (x && y) := by
  cases x <;> cases y <;> decide

theorem boolWord_or (x y : Bool) : boolWord x ||| boolWord y = boolWord (x || y) := by
  cases x <;> cases y <;> decide

theorem boolWord_not (x : Bool) :
    UInt64.ofNat ((if boolWord x = 0 then (1 : UInt32) else 0).toNat) = boolWord (!x) := by
  cases x <;> decide

theorem widthSum_cons (t : Ty) (ts : List Ty) : widthSum (t :: ts) = t.width + widthSum ts := by
  simp [widthSum]

theorem Env.values_length {Γ : List Ty} (env : Env Γ) : env.values.length = widthSum Γ := by
  induction env with
  | nil => rfl
  | @cons Γ t v rest ih => simp [Env.values, ih, widthSum_cons, Ty.values_length]

/-- The functions that `funs` gives are the module's functions at their call indices, each
returning its value without a trap and keeping the store. -/
def Calls {S : List Sig} (m : Module) (funs : Funs S) : Prop :=
  ∀ {ps : List Ty} {r : Ty} (g : FVar S ps r),
    ImplementsPureA false m g.callIndex (funs.get g) ∧
      ∃ fn, m.funcs[g.callIndex]? = some fn ∧ fn.numParams = widthSum ps

theorem le_argsMax : {ps : List Ty} → (w : (i : Fin ps.length) → Nat) →
    (i : Fin ps.length) → w i ≤ argsMax w
  | _ :: _, w, ⟨0, _⟩ => Nat.le_max_left _ _
  | _ :: _, w, ⟨i + 1, h⟩ =>
    (le_argsMax (fun j => w j.succ) ⟨i, by simpa using h⟩).trans (Nat.le_max_right _ _)

/-- The code of an expression pushes the words of its value, in the frames that
`Expr.code_spec` describes. -/
def CodeSpec {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (host : HostEnv Unit) (store : Store Unit) (e : Expr S Γ t) (env : Env Γ) (locs : List Nat) :
    Prop :=
  ∀ (base : Nat) (s : Locals), Holds env locs base s → s.params.length ≤ base →
    base + e.width ≤ s.params.length + s.locals.length →
    ∀ (rest : Program) (Q : Assertion Unit),
    (∀ s', Frame base s s' →
      wp m rest Q store { s' with values := (t.values (e.denote funs env)).reverse ++ s.values }
        host) →
    wp m (e.code locs base ++ rest) Q store s host

/-- The code of a call's arguments pushes the words of their values, in order, when the code of
each argument does. -/
theorem args_spec {S : List Sig} {Γ : List Ty} (m : Module) (funs : Funs S) (host : HostEnv Unit)
    (store : Store Unit) {ps : List Ty} (args : (i : Fin ps.length) → Expr S Γ (ps.get i))
    (env : Env Γ) (locs : List Nat) (base : Nat) (s : Locals) (hVars : Holds env locs base s)
    (hBase : s.params.length ≤ base)
    (hRoom : ∀ i, base + (args i).width ≤ s.params.length + s.locals.length)
    (hSpec : ∀ i, CodeSpec m funs host store (args i) env locs) (rest : Program)
    (Q : Assertion Unit)
    (hNext : ∀ s', Frame base s s' →
      wp m rest Q store
        { s' with values := (Env.ofFn fun i => (args i).denote funs env).values.reverse ++
            s.values } host) :
    wp m (argsCode (fun i => (args i).code locs base) ++ rest) Q store s host := by
  induction ps generalizing s rest Q with
  | nil => simpa [argsCode, Env.ofFn, Env.values] using hNext s (Frame.refl base s)
  | cons p ps ih =>
    simp only [argsCode, List.append_assoc]
    refine hSpec ⟨0, by simp⟩ base s hVars hBase (hRoom _) _ _ fun s1 h1 => ?_
    have hp1 : s1.params = s.params := h1.params
    have hl1 : s1.locals.length = s.locals.length := h1.length
    refine ih (fun i => args i.succ)
      { s1 with values := (Ty.values p ((args ⟨0, by simp⟩).denote funs env)).reverse ++
          s.values }
      (hVars.frame h1 le_rfl : Holds env locs base s1)
      (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
      (fun i => by
        show base + (args i.succ).width ≤ s1.params.length + s1.locals.length
        rw [hp1, hl1]; exact hRoom _)
      (fun i => hSpec i.succ) _ _ fun s2 h2 => ?_
    simpa [Env.ofFn, Env.values, List.append_assoc, List.getElem_cons_zero] using
      hNext s2 (h1.trans h2.values)

/-- The code of an expression pushes the words of the expression's value from any frame in
which every variable holds its words in its locals below `base` and the locals from `base` on are
free.  It changes no parameter and no local below `base`. -/
theorem Expr.code_spec {S : List Sig} {Γ : List Ty} {t : Ty} (m : Module) (funs : Funs S)
    (hImports : m.imports = []) (hCalls : Calls m funs) (expr : Expr S Γ t) (env : Env Γ)
    (locs : List Nat) (base : Nat) (host : HostEnv Unit) (store : Store Unit) (s : Locals)
    (hVars : Holds env locs base s) (hBase : s.params.length ≤ base)
    (hRoom : base + expr.width ≤ s.params.length + s.locals.length) (rest : Program)
    (Q : Assertion Unit)
    (hNext : ∀ s', Frame base s s' →
      wp m rest Q store
        { s' with values := (t.values (expr.denote funs env)).reverse ++ s.values } host) :
    wp m (expr.code locs base ++ rest) Q store s host := by
  induction expr generalizing locs base s rest Q with
  | word value =>
      simpa [Expr.code, Expr.denote] using hNext s (Frame.refl base s)
  | bool value =>
      simpa [Expr.code, Expr.denote] using hNext s (Frame.refl base s)
  | @var Γ' tTy x =>
      simp only [Expr.code]
      exact wp_loadCode _ (Ty.values_length _ _) (hVars _ x).2 (hNext s (Frame.refl base s))
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
        let s1a := setLocal { s1 with values := s.values } base (.i64 (left.denote funs env))
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
        let s2b := setLocal { s2 with values := s.values } (base + 1) (.i64 (right.denote funs env))
        show wp m _ Q store s2b host
        have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote funs env)) :=
          Locals.get_setLocal_same (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
            (by show base + 1 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega)
        have hLeftSlot : s2b.get base = some (.i64 (left.denote funs env)) := by
          calc s2b.get base = s2.get base :=
                Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
                  (by omega)
            _ = s1a.get base := h2.below base (by omega)
            _ = some (.i64 (left.denote funs env)) :=
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
        by_cases hZero : right.denote funs env = 0
        · simp only [hZero, ite_true, ne_eq]
          simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
            hNext s2b hFrame
        · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
          simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
            hNext s2b hFrame
      all_goals
        simp only [BinOp.scratch, Nat.zero_add] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, Nat.add_zero, List.append_assoc]
        refine leftSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
        have hp1 : s1.params = s.params := h1.params
        have hl1 : s1.locals.length = s.locals.length := h1.length
        refine rightSpec env locs base
          { s1 with values := .i64 (left.denote funs env) :: s.values }
          (hVars.frame h1 le_rfl : Holds env locs base s1)
          (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
          (by show base + right.width ≤ s1.params.length + s1.locals.length
              rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
        have hFrame : Frame base s s2 := h1.trans h2.values
        simpa [Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
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
        { s1 with values := .i64 (left.denote funs env) :: s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + right.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      have hFrame : Frame base s s2 := h1.trans h2.values
      have hv := hNext s2 hFrame
      simp only [rev_values_word]
      cases op <;>
        simp only [CmpOp.instr, wp_eqI64_cons, wp_neI64_cons, wp_ltUI64_cons, wp_leUI64_cons,
          wp_extendUI32_cons]
      · by_cases hab : left.denote funs env = right.denote funs env <;>
          simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
      · by_cases hab : left.denote funs env = right.denote funs env <;>
          simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
      · by_cases hab : left.denote funs env < right.denote funs env <;>
          simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
      · by_cases hab : left.denote funs env ≤ right.denote funs env <;>
          simpa [hab, Expr.denote, CmpOp.apply, boolWord] using hv
  | not e eSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine eSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      simp only [rev_values_bool, wp_eqzI64_cons, wp_extendUI32_cons, boolWord_not]
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
        { s1 with values := .i64 (boolWord (left.denote funs env)) :: s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + right.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      simp only [rev_values_bool, wp_andI64_cons, boolWord_and]
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
        { s1 with values := .i64 (boolWord (left.denote funs env)) :: s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + right.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      simp only [rev_values_bool, wp_orI64_cons, boolWord_or]
      simpa [Expr.denote] using hNext s2 (h1.trans h2.values)
  | @ite Γ' tTy c thenE elseE cSpec thenSpec elseSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hc : c.width ≤ max c.width (tTy.width + max thenE.width elseE.width) :=
        Nat.le_max_left ..
      have hb : tTy.width + max thenE.width elseE.width ≤
          max c.width (tTy.width + max thenE.width elseE.width) := Nat.le_max_right ..
      have ht : thenE.width ≤ max thenE.width elseE.width := Nat.le_max_left ..
      have he : elseE.width ≤ max thenE.width elseE.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine cSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      simp only [rev_values_bool, wp_eqzI64_cons]
      rw [wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      have hVars1 : Holds env locs (base + tTy.width) { s1 with values := s.values } :=
        (hVars.frame h1 le_rfl : Holds env locs base s1).mono (by omega)
      have hBase1 :
          ({ s1 with values := s.values } : Locals).params.length ≤ base + tTy.width := by
        show s1.params.length ≤ base + tTy.width; rw [hp1]; omega
      -- Each branch: its code, the store of its words, and the load after the `if`.
      have branch : ∀ (b : Expr S Γ' tTy), (∀ (locs : List Nat) (base : Nat) (s : Locals),
          Holds env locs base s → s.params.length ≤ base →
          base + b.width ≤ s.params.length + s.locals.length → ∀ (rest : Program)
          (Q : Assertion Unit), (∀ s', Frame base s s' →
            wp m rest Q store
              { s' with values := (tTy.values (b.denote funs env)).reverse ++ s.values } host) →
          wp m (b.code locs base ++ rest) Q store s host) →
          b.width ≤ max thenE.width elseE.width →
          (tTy.values (b.denote funs env) =
            tTy.values ((Expr.ite c thenE elseE).denote funs env)) →
          ∀ (Qb : Assertion Unit), (∀ s', wp m (loadCode base tTy.width ++ rest) Q store
            { s' with values := s.values } host → Qb (.Fallthrough store s')) →
          wp m (b.code locs (base + tTy.width) ++ storeCode base tTy.width) Qb store
            { s1 with values := s.values } host := by
        intro b bSpec hbw hval Qb hQb
        rw [← List.append_nil (storeCode base tTy.width)]
        refine bSpec locs (base + tTy.width) _ hVars1 hBase1
          (by show base + tTy.width + b.width ≤ s1.params.length + s1.locals.length
              rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
        have hp2 : s2.params = s.params := h2.params.trans hp1
        have hl2 : s2.locals.length = s.locals.length := h2.length.trans hl1
        refine wp_storeCode _ base tTy.width s2 s.values (Ty.values_length _ _)
          (by rw [hp2]; omega) (by rw [hp2, hl2]; omega) fun s3 hp3 hl3 hold hout => ?_
        rw [wp_nil]
        refine hQb _ (wp_loadCode _ (Ty.values_length _ _) hold ?_)
        have hFrame : Frame base s { s3 with values := s.values } := by
          refine ⟨hp3.trans hp2, hl3.trans hl2, fun j hj => ?_⟩
          show s3.get j = s.get j
          rw [hout j (Or.inl hj), h2.below j (by omega)]
          exact h1.below j hj
        rw [hval]
        exact hNext _ hFrame
      cases hcv : c.denote funs env
      · simp (config := { decide := true }) only [↓reduceIte]
        exact branch elseE (fun locs base s hV hB hR rest Q hN =>
          elseSpec env locs base s hV hB hR rest Q hN) he (by simp [Expr.denote, hcv]) _
          fun s' h => by simpa using h
      · simp (config := { decide := true }) only [↓reduceIte]
        exact branch thenE (fun locs base s hV hB hR rest Q hN =>
          thenSpec env locs base s hV hB hR rest Q hN) ht (by simp [Expr.denote, hcv]) _
          fun s' h => by simpa using h
  | @letE Γ' sTy tTy value body valueSpec bodySpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
      have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc]
      refine valueSpec env locs (base + sTy.width) s (hVars.mono (by omega)) (by omega)
        (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine wp_storeCode _ base sTy.width s1 s.values (Ty.values_length _ _)
        (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) fun s2 hp2 hl2 hold hout => ?_
      have hVars2 : Holds (Env.cons (value.denote funs env) env) (base :: locs)
          (base + sTy.width) { s2 with values := s.values } :=
        (hVars.agree (s' := { s2 with values := s.values }) fun j hj => by
          show s2.get j = s.get j
          rw [hout j (Or.inl hj)]
          exact h1.below j (by omega)).push hold
      refine bodySpec (Env.cons (value.denote funs env) env) (base :: locs) (base + sTy.width)
        { s2 with values := s.values } hVars2
        (by show s2.params.length ≤ base + sTy.width; rw [hp2, hp1]; omega)
        (by show base + sTy.width + body.width ≤ s2.params.length + s2.locals.length
            rw [hp2, hl2, hp1, hl1]; omega) _ _ fun s3 h3 => ?_
      have hFrame : Frame base s s3 := by
        refine ⟨h3.params.trans (hp2.trans hp1), h3.length.trans (hl2.trans hl1),
          fun j hj => ?_⟩
        rw [h3.below j (by omega)]
        show s2.get j = s.get j
        rw [hout j (Or.inl hj)]
        exact h1.below j (by omega)
      exact hNext s3 hFrame
  | @call ps r Γ' g args argsSpec =>
      have hRoom' : ∀ i, base + (args i).width ≤ s.params.length + s.locals.length := fun i =>
        (Nat.add_le_add_left (le_argsMax (fun i => (args i).width) i) base).trans hRoom
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine args_spec m funs host store args env locs base s hVars hBase hRoom'
        (fun i base' s' hV hB hR rest' Q' hN => argsSpec i env locs base' s' hV hB hR rest' Q' hN)
        _ _ fun s1 h1 => ?_
      obtain ⟨hImpl, fn, hfn, hnum⟩ := hCalls g
      have hRun := (hImpl host store (Env.ofFn fun i => (args i).denote funs env)).append_args
        (by simp [hImports]) (by simpa [hImports] using hfn)
        (by simp [Scalar.values, Env.values_length, hnum]) s.values
      refine wp_call_runs (aborts := false) hRun trivial fun st' vs hPost => ?_
      obtain ⟨out, hvs, hst, hout⟩ := hPost
      have hout' : out = (Ty.values r (funs.get g
          (Env.ofFn fun i => (args i).denote funs env))).reverse := by
        have := congrArg List.reverse hout
        simpa [Scalar.values] using this
      subst hvs hst hout'
      exact hNext s1 h1
  | @pair Γ' sTy tTy first second firstSpec secondSpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hFirstRoom : first.width ≤ max first.width second.width := Nat.le_max_left ..
      have hSecondRoom : second.width ≤ max first.width second.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc]
      refine firstSpec env locs base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine secondSpec env locs base
        { s1 with values := (sTy.values (first.denote funs env)).reverse ++ s.values }
        (hVars.frame h1 le_rfl : Holds env locs base s1)
        (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
        (by show base + second.width ≤ s1.params.length + s1.locals.length
            rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
      simpa [Expr.denote, List.reverse_append, List.append_assoc] using
        hNext s2 (h1.trans h2.values)
  | @letPair Γ' sTy tTy uTy e body eSpec bodySpec =>
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hERoom : e.width ≤ max e.width body.width := Nat.le_max_left ..
      have hBodyRoom : body.width ≤ max e.width body.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc]
      refine eSpec env locs (base + sTy.width + tTy.width) s (hVars.mono (by omega)) (by omega)
        (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      rw [show (Ty.values (.pair sTy tTy) (e.denote funs env)).reverse ++ s.values =
          (tTy.values (e.denote funs env).2).reverse ++
            ((sTy.values (e.denote funs env).1).reverse ++ s.values) by
        simp [List.reverse_append, List.append_assoc]]
      refine wp_storeCode _ (base + sTy.width) tTy.width s1 _ (Ty.values_length _ _)
        (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) fun s2 hp2 hl2 hold2 hout2 => ?_
      refine wp_storeCode _ base sTy.width s2 s.values (Ty.values_length _ _)
        (by rw [hp2, hp1]; omega) (by rw [hp2, hl2, hp1, hl1]; omega)
        fun s3 hp3 hl3 hold3 hout3 => ?_
      have hbelow : ∀ j < base, ({ s3 with values := s.values } : Locals).get j = s.get j := by
        intro j hj
        show s3.get j = s.get j
        rw [hout3 j (Or.inl hj), hout2 j (Or.inl (by omega))]
        exact h1.below j (by omega)
      have hold2' : LocalsHold { s3 with values := s.values } (base + sTy.width)
          (tTy.values (e.denote funs env).2) := by
        intro k hk
        show s3.get (base + sTy.width + k) = _
        rw [hout3 _ (Or.inr (by omega))]
        exact hold2 k hk
      have hVars3 := ((hVars.agree hbelow).push (v := (e.denote funs env).1) hold3).push
        (v := (e.denote funs env).2) hold2'
      refine bodySpec (Env.cons (e.denote funs env).2 (Env.cons (e.denote funs env).1 env))
        ((base + sTy.width) :: base :: locs) (base + sTy.width + tTy.width)
        { s3 with values := s.values } hVars3
        (by show s3.params.length ≤ base + sTy.width + tTy.width; rw [hp3, hp2, hp1]; omega)
        (by show base + sTy.width + tTy.width + body.width ≤
              s3.params.length + s3.locals.length
            rw [hp3, hl3, hp2, hl2, hp1, hl1]; omega) _ _ fun s4 h4 => ?_
      have hFrame : Frame base s s4 := by
        refine ⟨h4.params.trans (hp3.trans (hp2.trans hp1)),
          h4.length.trans (hl3.trans (hl2.trans hl1)), fun j hj => ?_⟩
        rw [h4.below j (by omega)]
        exact hbelow j hj
      exact hNext s4 hFrame

theorem Var.index_lt {Γ : List Ty} {t : Ty} (x : Var Γ t) : x.index < Γ.length := by
  induction x with
  | here => simp [Var.index]
  | there y ih => simp [Var.index]; omega

/-- The position of a variable's first word among the words of the context's values. -/
def Var.offset : {Γ : List Ty} → {t : Ty} → Var Γ t → Nat
  | _ :: _, _, .here => 0
  | s :: _, _, .there y => s.width + y.offset

theorem paramLocs_getD {Γ : List Ty} {t : Ty} (x : Var Γ t) (loc : Nat) :
    (paramLocs Γ loc).getD x.index 0 = loc + x.offset := by
  induction x generalizing loc with
  | here => simp [paramLocs, Var.index, Var.offset]
  | @there Γ' t' s' y ih =>
    simp only [paramLocs, Var.index, Var.offset, List.getD_cons_succ, ih]
    omega

theorem Var.offset_width {Γ : List Ty} {t : Ty} (x : Var Γ t) :
    x.offset + t.width ≤ widthSum Γ := by
  induction x with
  | here => simp [Var.offset, widthSum_cons]
  | @there Γ' t' s' y ih => simp only [Var.offset, widthSum_cons]; omega

theorem Env.values_get {Γ : List Ty} {t : Ty} (env : Env Γ) (x : Var Γ t) (k : Nat)
    (hk : k < t.width) : env.values[x.offset + k]? = (t.values (env.get x))[k]? := by
  induction x with
  | here =>
    cases env with
    | cons v rest =>
      simp only [Env.values, Var.offset, Env.get, Nat.zero_add]
      rw [List.getElem?_append_left (by rw [Ty.values_length]; exact hk)]
  | @there Γ' t' s' y ih =>
    cases env with
    | cons v rest =>
      simp only [Env.values, Var.offset, Env.get]
      rw [List.getElem?_append_right (by rw [Ty.values_length]; omega), Ty.values_length,
        show s'.width + y.offset + k - s'.width = y.offset + k by omega]
      exact ih rest hk

theorem FVar.index_lt {S : List Sig} {ps : List Ty} {r : Ty} (f : FVar S ps r) :
    f.index < S.length := by
  induction f with
  | here => simp [FVar.index]
  | there g ih => simp [FVar.index]; omega

/-- A function at position `pos` of a module whose functions at the call indices compute the
functions it calls returns `func.denote funs args`, without a trap, from any store, and leaves
the store unchanged. -/
theorem Func.correct {S : List Sig} (func : Func S) (funs : Funs S) (m : Module) (pos : Nat)
    (hImports : m.imports = []) (hFunc : m.funcs[pos]? = some (func.function pos))
    (hCalls : Calls m funs) :
    ImplementsPureA false m pos (func.denote funs) := by
  intro host store args
  have hLength : (Scalar.values args).length = widthSum func.params := by
    simp [Scalar.values, Env.values_length]
  apply Runs.of_wp_entry_for (f := func.function pos)
    (by rw [hImports, List.length_nil, Nat.sub_zero]; exact hFunc) (hImp := by simp [hImports])
  have hTake : ((Scalar.values args).reverse.take (func.function pos).numParams).reverse =
      Scalar.values args := by
    rw [List.take_of_length_le (by simp [Func.function, Func.type, Function.numParams, hLength])]
    simp
  rw [hTake, show (func.function pos).body =
    func.body.code (paramLocs func.params 0) (widthSum func.params) ++ [] by
      simp [Func.function]]
  refine Expr.code_spec m funs hImports hCalls func.body args (paramLocs func.params 0)
    (widthSum func.params) host store _ (fun _ x => ?_) (by simp [Function.toLocals, hLength])
    (by simp [Function.toLocals, Func.function, hLength]) [] _ fun s' _ => ?_
  · have hx := x.offset_width
    rw [paramLocs_getD x 0, Nat.zero_add]
    refine ⟨hx, fun k hk => ?_⟩
    rw [Ty.values_length] at hk
    have hv := args.values_get x k hk
    have hlt : x.offset + k < args.values.length := by rw [Env.values_length]; omega
    simp only [Locals.get, Function.toLocals, Scalar.values, hlt, ↓reduceIte]
    rw [hv, List.getElem?_eq_getElem (by rw [Ty.values_length]; exact hk)]
  · simp [Func.function, Func.type, Function.numParams, Func.denote, Scalar.values,
      Env.values_length, Ty.values_length]

/-- Every function of a program, placed from position 2 of a module without imports, computes
its meaning. -/
theorem Prog.calls {S : List Sig} (prog : Prog S) (m : Module) (hImports : m.imports = [])
    (hFuncs : ∀ k < S.length, m.funcs[2 + k]? = prog.functions[k]?) : Calls m prog.funs := by
  induction prog with
  | nil => intro ps r g; cases g
  | @cons S' f rest ih =>
    have hRest : Calls m rest.funs := ih fun k hk => by
      rw [hFuncs k (by simp; omega)]
      simp [Prog.functions, List.getElem?_append_left (by rw [rest.functions_length]; exact hk)]
    intro ps r g
    cases g with
    | here =>
      have hpos : m.funcs[2 + S'.length]? = some (f.function (2 + S'.length)) := by
        rw [hFuncs _ (by simp)]
        simp [Prog.functions, rest.functions_length]
      refine ⟨?_, f.function (2 + S'.length), ?_, ?_⟩
      · simpa [FVar.callIndex, FVar.index, Funs.get, Prog.funs] using
          Func.correct f rest.funs m _ hImports hpos hRest
      · simpa [FVar.callIndex, FVar.index] using hpos
      · simp [Func.function, Func.type, Function.numParams]
    | there g' =>
      obtain ⟨h1, fn, h2, h3⟩ := hRest g'
      have hidx : (FVar.there g' : FVar ((f.params, f.result) :: S') ps r).callIndex =
          g'.callIndex := by
        have := g'.index_lt
        simp only [FVar.callIndex, FVar.index, List.length_cons]
        omega
      rw [hidx]
      exact ⟨by simpa [Funs.get, Prog.funs] using h1, fn, h2, h3⟩

/-- The correctness theorem.  Every function of a program's module returns, at its call index,
the value that the program gives it, without a trap, from any store, and leaves the store
unchanged. -/
theorem Prog.correct {S : List Sig} (prog : Prog S) : Calls (compile prog) prog.funs :=
  prog.calls _ rfl fun k _ => compile_funcs prog k

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
