import Verified.Wasi.FunctionDispatcher

namespace Verified.Wasi

open Wasm

theorem defined_function_run_post {World : Type} {target : Wasm.Module}
    {function : Wasm.Function} {index width : Nat} {params : List Value}
    {initial : Store World} {targetHost : HostEnv World} {post : Result World → Prop}
    (imports : target.imports = ABI.imports)
    (lookup : target.funcs[index]? = some function)
    (arity : params.length = function.numParams) (results : function.results.length = width)
    (body : wp target function.body (FunctionRunPost width post)
      initial (function.toLocals params) targetHost) :
    ∃ bound, ∀ fuel ≥ bound,
      post (run fuel target (3 + index) initial params.reverse targetHost) := by
  unfold wp at body
  obtain ⟨bound, enough⟩ := body
  have noImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [imports, ABI.imports_length]; omega)
  have take : (params.reverse.take function.numParams).reverse = params := by
    rw [List.take_of_length_le (by
      simpa only [List.length_reverse, arity] using (Nat.le_refl function.numParams)),
      List.reverse_reverse]
  have drop : params.reverse.drop function.numParams = [] :=
    List.drop_eq_nil_of_le (by
      simpa only [List.length_reverse, arity] using (Nat.le_refl function.numParams))
  refine ⟨bound, fun fuel hFuel => ?_⟩
  have proof := enough fuel hFuel
  rw [run_eq noImport]
  simp only [imports, ABI.imports_length, show 3 + index - 3 = index by omega,
    lookup, take, drop, results, List.append_nil]
  cases executed : exec fuel target initial (function.toLocals params) function.body targetHost with
  | Fallthrough final locals => simpa only [FunctionRunPost, executed] using proof
  | Trap final message => simpa only [FunctionRunPost, executed] using proof
  | Break label final locals => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | Return final values => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | Invalid message => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | OutOfFuel => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | ReturnCall entry final values => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | Throwing tag values final locals => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)

end Verified.Wasi
