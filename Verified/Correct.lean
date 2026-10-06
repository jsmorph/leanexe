import Verified.Compile
import LeanExe.TalosCompat

/-! The compiler's correctness theorem: for every function whose body reads only its arguments,
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

/-- The code of an expression pushes the expression's value from any frame whose parameters are
the arguments and whose locals from `base` on hold the expression's scratch.  It changes no
parameter and no local below `base`. -/
theorem Expr.code_spec (expr : Expr) (args : List UInt64) (h : expr.argsBelow args.length)
    (base : Nat) (m : Module) (env : HostEnv α) (store : Store α) (s : Locals)
    (hParams : s.params = args.map Value.i64) (hBase : args.length ≤ base)
    (hRoom : base + expr.width ≤ args.length + s.locals.length) (rest : Program)
    (Q : Assertion α)
    (hNext : ∀ s', Frame base s s' →
      wp m rest Q store { s' with values := .i64 (expr.denote args) :: s.values } env) :
    wp m (expr.code base ++ rest) Q store s env := by
  induction expr generalizing base s rest Q with
  | const value =>
      simpa [Expr.code, Expr.denote] using hNext s (Frame.refl base s)
  | arg index =>
      have hIndex : index < args.length := by simpa [Expr.argsBelow] using h
      have hValue : (Expr.arg index).denote args = args[index] := by
        simp [Expr.denote, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIndex]
      have hGet : s.get index = some (.i64 args[index]) := by
        simp [Locals.get, hParams, hIndex]
      have hNext' := hNext s (Frame.refl base s)
      rw [hValue] at hNext'
      simp only [Expr.code, List.cons_append, List.nil_append, wp_localGet_cons, hGet]
      exact hNext'
  | bin op left right leftSpec rightSpec =>
      simp only [Expr.argsBelow, Bool.and_eq_true] at h
      have hWidth := hRoom
      simp only [Expr.width] at hWidth
      have hLeftRoom : left.width ≤ max left.width right.width := Nat.le_max_left ..
      have hRightRoom : right.width ≤ max left.width right.width := Nat.le_max_right ..
      cases op
      case div | rem =>
        simp only [BinOp.scratch] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, List.append_assoc, List.cons_append,
          List.nil_append]
        refine leftSpec h.1 (base + 2) s hParams (by omega) (by omega) _ _ fun s1 h1 => ?_
        have hp1 : s1.params.length = args.length := by rw [h1.params, hParams]; simp
        have hl1 : s1.locals.length = s.locals.length := h1.length
        rw [wp_localSet_cons]
        simp only
        rw [Locals.set?_local (s := { s1 with values := .i64 (left.denote args) :: s.values })
          _ (by simp only; omega) (by simp only; omega)]
        simp only
        let s1a := setLocal { s1 with values := s.values } base (.i64 (left.denote args))
        have hp1a : s1a.params = args.map Value.i64 := by
          simp only [s1a, setLocal]; rw [h1.params, hParams]
        have hl1a : s1a.locals.length = s.locals.length := by
          simp [s1a, setLocal, hl1]
        refine rightSpec h.2 (base + 2) s1a hp1a (by omega) (by omega) _ _ fun s2 h2 => ?_
        have hp2 : s2.params.length = args.length := by rw [h2.params, hp1a]; simp
        have hl2 : s2.locals.length = s.locals.length := h2.length.trans hl1a
        rw [wp_localSet_cons]
        simp only
        rw [Locals.set?_local (s := { s2 with values := .i64 (right.denote args) :: s1a.values })
          _ (by simp only; omega) (by simp only; omega)]
        simp only
        let s2b := setLocal { s2 with values := s.values } (base + 1)
          (.i64 (right.denote args))
        have hRightSlot : s2b.get (base + 1) = some (.i64 (right.denote args)) :=
          Locals.get_setLocal_same (by simp only; omega) (by simp only; omega)
        have hLeftSlot : s2b.get base = some (.i64 (left.denote args)) := by
          calc s2b.get base = s2.get base := Locals.get_setLocal_ne (by simp only; omega) (by omega)
            _ = s1a.get base := h2.below base (by omega)
            _ = some (.i64 (left.denote args)) :=
              Locals.get_setLocal_same (by simp only; omega) (by simp only; omega)
        have hFrame : Frame base s s2b := by
          refine ⟨?_, ?_, fun j hj => ?_⟩
          · simp only [s2b, setLocal]; rw [h2.params, hp1a, hParams]
          · simp [s2b, setLocal, hl2]
          · calc s2b.get j = s2.get j := Locals.get_setLocal_ne (by simp only; omega) (by omega)
              _ = s1a.get j := h2.below j (by omega)
              _ = s1.get j := Locals.get_setLocal_ne (by simp only; omega) (by omega)
              _ = s.get j := h1.below j (by omega)
        let stored := setLocal { s2 with values := .i64 (right.denote args) :: s1a.values }
          (base + 1) (.i64 (right.denote args))
        have hState : ({ params := stored.params, locals := stored.locals, values := s1a.values } :
            Locals) = s2b := rfl
        rw [hState]
        have hs2b : s2b.values = s.values := rfl
        simp only [wp_localGet_cons, hRightSlot, wp_eqzI64_cons]
        rw [wp_iff_control_types]
        refine wp_iff_cons rfl ?_
        by_cases hZero : right.denote args = 0
        · simp only [hZero, ite_true, ne_eq]
          simpa [-Locals.get, hLeftSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
            hNext s2b hFrame
        · simp only [hZero, ite_false, ne_eq, not_true_eq_false]
          simpa [-Locals.get, hLeftSlot, hRightSlot, hZero, Expr.denote, BinOp.apply, hs2b] using
            hNext s2b hFrame
      all_goals
        simp only [BinOp.scratch, Nat.zero_add] at hWidth
        simp only [Expr.code, BinOp.code, BinOp.scratch, Nat.add_zero, List.append_assoc]
        refine leftSpec h.1 base s hParams hBase (by omega) _ _ fun s1 h1 => ?_
        have hl1 : s1.locals.length = s.locals.length := h1.length
        refine rightSpec h.2 base { s1 with values := .i64 (left.denote args) :: s.values }
          (h1.params.trans hParams) hBase (by simp only; omega) _ _ fun s2 h2 => ?_
        have hFrame : Frame base s s2 := h1.trans h2.values
        simpa [Expr.denote, BinOp.apply, ← UInt64.shiftLeft_eq_shiftLeft_mod,
          ← UInt64.shiftRight_eq_shiftRight_mod] using hNext s2 hFrame

/-- The correctness theorem.  Function `2 + i` of the compiled module returns
`func.denote args`, without a trap, from any store, and leaves the store unchanged. -/
theorem Func.correct (funcs : List (Func × String)) (i : Nat) (func : Func) (name : String)
    (hFunc : funcs[i]? = some (func, name)) (hArgs : func.body.argsBelow func.arity) :
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
  rw [hTake, show (func.function (2 + i)).body = func.body.code func.arity ++ [] by
    simp [Func.function]]
  refine Expr.code_spec func.body args.toList (by simpa using hArgs) func.arity _ env store _
    (by simp [Function.toLocals, Func.function, Scalar.values]) (by simp)
    (by simp [Function.toLocals, Func.function]) [] _ fun s' _ => ?_
  simp [Func.function, Func.type, Function.numParams, Func.denote, Scalar.values]

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
