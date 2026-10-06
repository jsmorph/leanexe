import Verified.Compile

/-! The compiler's correctness theorem: for every function whose body reads only its arguments,
the compiled module returns the function's value, without a trap, and leaves the store
unchanged. -/

namespace Verified

open Wasm LeanExe.Pipeline

/-- The code of an expression pushes the expression's value, from any frame whose parameters are
the arguments. -/
theorem Expr.code_spec (expr : Expr) (args : List UInt64) (h : expr.argsBelow args.length)
    (m : Module) (env : HostEnv α) (store : Store α) (s : Locals)
    (hParams : s.params = args.map Value.i64) (rest : Program) (Q : Assertion α)
    (hNext : wp m rest Q store { s with values := .i64 (expr.denote args) :: s.values } env) :
    wp m (expr.code ++ rest) Q store s env := by
  induction expr generalizing s rest Q with
  | const value =>
      simpa [Expr.code, Expr.denote] using hNext
  | arg index =>
      have hIndex : index < args.length := by simpa [Expr.argsBelow] using h
      have hValue : (Expr.arg index).denote args = args[index] := by
        simp [Expr.denote, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hIndex]
      have hGet : s.get index = some (.i64 args[index]) := by
        simp [Locals.get, hParams, hIndex, List.getElem?_map, List.getElem?_eq_getElem hIndex]
      rw [hValue] at hNext
      simp only [Expr.code, List.cons_append, List.nil_append, wp_localGet_cons, hGet]
      exact hNext
  | add left right leftSpec rightSpec =>
      simp only [Expr.argsBelow, Bool.and_eq_true] at h
      simp only [Expr.code, List.append_assoc]
      refine leftSpec h.1 s hParams _ _
        (rightSpec h.2 { s with values := .i64 (left.denote args) :: s.values } hParams _ _ ?_)
      simpa [Expr.denote] using hNext
  | sub left right leftSpec rightSpec =>
      simp only [Expr.argsBelow, Bool.and_eq_true] at h
      simp only [Expr.code, List.append_assoc]
      refine leftSpec h.1 s hParams _ _
        (rightSpec h.2 { s with values := .i64 (left.denote args) :: s.values } hParams _ _ ?_)
      simpa [Expr.denote] using hNext
  | mul left right leftSpec rightSpec =>
      simp only [Expr.argsBelow, Bool.and_eq_true] at h
      simp only [Expr.code, List.append_assoc]
      refine leftSpec h.1 s hParams _ _
        (rightSpec h.2 { s with values := .i64 (left.denote args) :: s.values } hParams _ _ ?_)
      simpa [Expr.denote] using hNext

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
  rw [hTake, show (func.function (2 + i)).body = func.body.code ++ [] by simp [Func.function]]
  refine Expr.code_spec func.body args.toList (by simpa using hArgs) _ env store _
    (by simp [Function.toLocals, Func.function, Scalar.values]) [] _ ?_
  simp [Func.function, Func.type, Function.numParams, hLength, Func.denote, Scalar.values]

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
