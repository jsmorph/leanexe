import Verified.Wasi.FunctionEntry

namespace Verified.Wasi

open Wasm

def FunctionRunPost (width : Nat) (post : Result World → Prop) : Assertion World
  | .Fallthrough final locals => post (.Success (locals.values.take width) final)
  | .Trap final message => post (.Trap final message)
  | _ => False

theorem effectFunction_run_post {World : Type} {source target : Module}
    {pureSigs : List Sig} {effectSigs : List EffectSig}
    {function : EffectFunc pureSigs effectSigs} {pool : Bytes.LiteralPool} {index typeIdx : Nat}
    {targetHost : HostEnv World} {initial : Store World} {depth : UInt64}
    {params : List Value} {post : Result World → Prop}
    (hImports : target.imports = ABI.imports)
    (hFunction : target.funcs[index]? = some (function.function source typeIdx pool))
    (length : params.length = widthSum function.params)
    (body : wp target (function.function source typeIdx pool).body
      (FunctionRunPost function.result.width post) initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: params)) targetHost) :
    ∃ bound, ∀ fuel ≥ bound,
      post (run fuel target (3 + index) initial (.i64 depth :: params).reverse targetHost) := by
  unfold wp at body
  obtain ⟨bound, hBound⟩ := body
  have hImport : target.imports[3 + index]? = none :=
    List.getElem?_eq_none (by rw [hImports, ABI.imports_length]; omega)
  have hNum : (function.function source typeIdx pool).numParams = 1 + widthSum function.params := by
    change (ValueType.i64 :: function.params.flatMap Ty.types).length = 1 + widthSum function.params
    rw [List.length_cons, flatMap_types_length]
    omega
  have hResults : (function.function source typeIdx pool).results.length = function.result.width := by
    change function.result.types.length = function.result.width
    cases function.result with
    | unit => rfl
    | value type => exact type.types_length
  have hTake : (((Value.i64 depth :: params).reverse).take
      (function.function source typeIdx pool).numParams).reverse = .i64 depth :: params := by
    rw [List.take_of_length_le (by
      rw [List.length_reverse, List.length_cons, length, hNum]
      omega), List.reverse_reverse]
  have hDrop : (Value.i64 depth :: params).reverse.drop
      (function.function source typeIdx pool).numParams = [] :=
    List.drop_eq_nil_of_le (by
      rw [List.length_reverse, List.length_cons, length, hNum]
      omega)
  refine ⟨bound, fun fuel enough => ?_⟩
  have proof := hBound fuel enough
  rw [run_eq hImport]
  simp only [hImports, ABI.imports_length, show 3 + index - 3 = index by omega,
    hFunction, hTake, hDrop, hResults, List.append_nil]
  cases executed : exec fuel target initial
      ((function.function source typeIdx pool).toLocals (.i64 depth :: params))
      (function.function source typeIdx pool).body targetHost with
  | Fallthrough final locals => simpa only [FunctionRunPost, executed] using proof
  | Trap final message => simpa only [FunctionRunPost, executed] using proof
  | Break label final locals => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | Return final values => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | Invalid message => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | OutOfFuel => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | ReturnCall entry final values => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)
  | Throwing tag values final locals => exact False.elim (by simpa only [FunctionRunPost, executed] using proof)

end Verified.Wasi
