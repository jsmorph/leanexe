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

/-- Variable `i`, for each `i` below the number of values, is in local `vars.getD i 0`, below
`base`, and that local holds `vals.getD i 0`. -/
def Holds (vals : List UInt64) (vars : List Nat) (base : Nat) (s : Locals) : Prop :=
  ∀ i < vals.length, vars.getD i 0 < base ∧ s.get (vars.getD i 0) = some (.i64 (vals.getD i 0))

theorem Holds.mono {vals : List UInt64} {vars : List Nat} {base base' : Nat} {s : Locals}
    (h : Holds vals vars base s) (hb : base ≤ base') : Holds vals vars base' s :=
  fun i hi => ⟨by have := (h i hi).1; omega, (h i hi).2⟩

theorem Holds.frame {vals : List UInt64} {vars : List Nat} {base base' : Nat} {s s' : Locals}
    (h : Holds vals vars base s) (hf : Frame base' s s') (hb : base ≤ base') :
    Holds vals vars base s' :=
  fun i hi => ⟨(h i hi).1, by rw [hf.below _ (by have := (h i hi).1; omega)]; exact (h i hi).2⟩

theorem Holds.setLocal {vals : List UInt64} {vars : List Nat} {base i : Nat} {s : Locals}
    {v : Value} (h : Holds vals vars base s) (hi : base ≤ i) (hLow : s.params.length ≤ i) :
    Holds vals vars base (setLocal s i v) :=
  fun j hj => ⟨(h j hj).1, by
    rw [Locals.get_setLocal_ne hLow (by have := (h j hj).1; omega)]; exact (h j hj).2⟩

/-- A `letE` adds its value, in local `base`, as the next variable. -/
theorem Holds.push {vals : List UInt64} {vars : List Nat} {base : Nat} {s : Locals} {x : UInt64}
    (h : Holds vals vars base s) (hLen : vars.length = vals.length)
    (hx : s.get base = some (.i64 x)) : Holds (vals ++ [x]) (vars ++ [base]) (base + 1) s := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  rcases Nat.lt_or_ge i vals.length with hlt | hge
  · have hvars : (vars ++ [base]).getD i 0 = vars.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < vars.length by omega)]
    have hvals : (vals ++ [x]).getD i 0 = vals.getD i 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
    rw [hvars, hvals]
    exact ⟨by have := (h i hlt).1; omega, (h i hlt).2⟩
  · obtain rfl : i = vals.length := by omega
    have hvars : (vars ++ [base]).getD vals.length 0 = base := by
      simp [List.getD_eq_getElem?_getD, ← hLen]
    have hvals : (vals ++ [x]).getD vals.length 0 = x := by
      simp [List.getD_eq_getElem?_getD]
    rw [hvars, hvals]
    exact ⟨by omega, hx⟩

/-- The code of an expression pushes the expression's value from any frame in which every
variable in scope is in its local below `base` and the locals from `base` on are free.  It
changes no parameter and no local below `base`. -/
theorem Expr.code_spec (expr : Expr) (vals : List UInt64) (vars : List Nat)
    (hLen : vars.length = vals.length) (h : expr.scoped vals.length) (base : Nat) (m : Module)
    (env : HostEnv α) (store : Store α) (s : Locals) (hVars : Holds vals vars base s)
    (hBase : s.params.length ≤ base)
    (hRoom : base + expr.width ≤ s.params.length + s.locals.length) (rest : Program)
    (Q : Assertion α)
    (hNext : ∀ s', Frame base s s' →
      wp m rest Q store { s' with values := .i64 (expr.denote vals) :: s.values } env) :
    wp m (expr.code vars base ++ rest) Q store s env := by
  induction expr generalizing vals vars base s rest Q with
  | const value =>
      simpa [Expr.code, Expr.denote] using hNext s (Frame.refl base s)
  | var index =>
      have hIndex : index < vals.length := by simpa [Expr.scoped] using h
      have hNext' := hNext s (Frame.refl base s)
      simp only [Expr.code, List.cons_append, List.nil_append, wp_localGet_cons,
        (hVars index hIndex).2]
      simpa [Expr.denote] using hNext'
  | bin op left right leftSpec rightSpec =>
      simp only [Expr.scoped, Bool.and_eq_true] at h
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
      have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
      cases op
      case div | rem =>
        simp only [BinOp.scratch] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, List.append_assoc, List.cons_append,
          List.nil_append]
        refine leftSpec vals vars hLen h.1 (base + 2) s (hVars.mono (by omega)) (by omega)
          (by omega) _ _ fun s1 h1 => ?_
        have hp1 : s1.params = s.params := h1.params
        have hl1 : s1.locals.length = s.locals.length := h1.length
        refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
        let s1a := setLocal { s1 with values := s.values } base (.i64 (left.denote vals))
        have hp1a : s1a.params = s.params := hp1
        have hl1a : s1a.locals.length = s.locals.length := by simp [s1a, setLocal, hl1]
        have hVars1a : Holds vals vars (base + 2) s1a :=
          ((hVars.frame h1 (by omega)).setLocal (le_refl _)
            (by show s1.params.length ≤ base; rw [hp1]; exact hBase)).mono (by omega)
        refine rightSpec vals vars hLen h.2 (base + 2) s1a hVars1a (by rw [hp1a]; omega)
          (by rw [hp1a, hl1a]; omega) _ _ fun s2 h2 => ?_
        have hp2 : s2.params = s.params := h2.params.trans hp1a
        have hl2 : s2.locals.length = s.locals.length := h2.length.trans hl1a
        refine wp_localSet_local (by rw [hp2]; omega) (by rw [hp2, hl2]; omega) ?_
        let s2b := setLocal { s2 with values := s.values } (base + 1)
          (.i64 (right.denote vals))
        show wp m _ Q store s2b env
        have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote vals)) :=
          Locals.get_setLocal_same (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
            (by show base + 1 < s2.params.length + s2.locals.length; rw [hp2, hl2]; omega)
        have hLeftSlot : s2b.get base = some (.i64 (left.denote vals)) := by
          calc s2b.get base = s2.get base :=
                Locals.get_setLocal_ne (by show s2.params.length ≤ base + 1; rw [hp2]; omega)
                  (by omega)
            _ = s1a.get base := h2.below base (by omega)
            _ = some (.i64 (left.denote vals)) :=
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
        by_cases hZero : right.denote vals = 0
        · simp only [hZero, ite_true, ne_eq]
          simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
            hNext s2b hFrame
        · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
          simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
            hNext s2b hFrame
      all_goals
        simp only [BinOp.scratch, Nat.zero_add] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, Nat.add_zero, List.append_assoc]
        refine leftSpec vals vars hLen h.1 base s hVars hBase (by omega) _ _ fun s1 h1 => ?_
        have hp1 : s1.params = s.params := h1.params
        have hl1 : s1.locals.length = s.locals.length := h1.length
        refine rightSpec vals vars hLen h.2 base
          { s1 with values := .i64 (left.denote vals) :: s.values }
          (hVars.frame h1 le_rfl : Holds vals vars base s1)
          (by show s1.params.length ≤ base; rw [hp1]; exact hBase)
          (by show base + right.width ≤ s1.params.length + s1.locals.length
              rw [hp1, hl1]; omega) _ _ fun s2 h2 => ?_
        have hFrame : Frame base s s2 := h1.trans h2.values
        simpa [Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
          ← UInt64.shiftRight_eq_shiftRight_mod] using hNext s2 hFrame
  | letE value body valueSpec bodySpec =>
      simp only [Expr.scoped, Bool.and_eq_true] at h
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hValueRoom : value.width ≤ max value.width body.width := Nat.le_max_left ..
      have hBodyRoom : body.width ≤ max value.width body.width := Nat.le_max_right ..
      simp only [Expr.code, List.append_assoc, List.cons_append, List.nil_append]
      refine valueSpec vals vars hLen h.1 (base + 1) s (hVars.mono (by omega)) (by omega)
        (by omega) _ _ fun s1 h1 => ?_
      have hp1 : s1.params = s.params := h1.params
      have hl1 : s1.locals.length = s.locals.length := h1.length
      refine wp_localSet_local (by rw [hp1]; omega) (by rw [hp1, hl1]; omega) ?_
      let s1a := setLocal { s1 with values := s.values } base (.i64 (value.denote vals))
      show wp m _ Q store s1a env
      have hp1a : s1a.params = s.params := hp1
      have hl1a : s1a.locals.length = s.locals.length := by simp [s1a, setLocal, hl1]
      have hSlot : s1a.get base = some (.i64 (value.denote vals)) :=
        Locals.get_setLocal_same (by show s1.params.length ≤ base; rw [hp1]; omega)
          (by show base < s1.params.length + s1.locals.length; rw [hp1, hl1]; omega)
      have hVars1a : Holds (vals ++ [value.denote vals]) (vars ++ [base]) (base + 1) s1a :=
        ((hVars.frame h1 (by omega)).setLocal (le_refl _)
          (by show s1.params.length ≤ base; rw [hp1]; exact hBase)).push hLen hSlot
      refine bodySpec (vals ++ [value.denote vals]) (vars ++ [base]) (by simp [hLen])
        (by simpa using h.2) (base + 1) s1a hVars1a (by rw [hp1a]; omega)
        (by rw [hp1a, hl1a]; omega) _ _ fun s2 h2 => ?_
      have hFrame : Frame base s s2 := by
        refine ⟨h2.params.trans hp1a, h2.length.trans hl1a, fun j hj => ?_⟩
        calc s2.get j = s1a.get j := h2.below j (by omega)
          _ = s1.get j :=
              Locals.get_setLocal_ne (by show s1.params.length ≤ base; rw [hp1]; omega)
                (by omega)
          _ = s.get j := h1.below j (by omega)
      have hs1a : s1a.values = s.values := rfl
      simpa [Expr.denote, hs1a] using hNext s2 hFrame

/-- The correctness theorem.  Function `2 + i` of the compiled module returns
`func.denote args`, without a trap, from any store, and leaves the store unchanged. -/
theorem Func.correct (funcs : List (Func × String)) (i : Nat) (func : Func) (name : String)
    (hFunc : funcs[i]? = some (func, name)) (hScoped : func.body.scoped func.arity) :
    ImplementsPureA false (compile funcs) (2 + i) func.denote := by
  intro env store args
  have hLength : (Scalar.values args).length = func.arity := by
    simp [Scalar.values]
  have hNoImports : (compile funcs).imports = [] := rfl
  apply Runs.of_wp_entry_for (f := func.function (2 + i))
    (by rw [hNoImports, List.length_nil, Nat.sub_zero]; exact compile_funcs hFunc)
  have hTake : ((Scalar.values args).reverse.take (func.function (2 + i)).numParams).reverse =
      Scalar.values args := by
    rw [List.take_of_length_le (by simp [Func.function, Func.type, Function.numParams, hLength])]
    simp
  rw [hTake, show (func.function (2 + i)).body =
    func.body.code (List.range func.arity) func.arity ++ [] by simp [Func.function]]
  refine Expr.code_spec func.body args.toList (List.range func.arity) (by simp)
    (by simpa using hScoped) func.arity _ env store _ (fun j hj => ?_)
    (by simp [Function.toLocals, Scalar.values])
    (by simp [Function.toLocals, Func.function, Scalar.values]) [] _ fun s' _ => ?_
  · have hj' : j < func.arity := by simpa using hj
    refine ⟨by simp [List.getD_eq_getElem?_getD, hj'], ?_⟩
    simp [Locals.get, Function.toLocals, Scalar.values, List.getD_eq_getElem?_getD, hj']
  · simp [Func.function, Func.type, Function.numParams, Func.denote, Scalar.values]

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
