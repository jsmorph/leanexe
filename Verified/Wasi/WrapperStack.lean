import Verified.Wasi.WrapperDispatch

namespace Verified.Wasi

open Wasm

theorem wp_wrapper_localGets {World : Type} {target : Wasm.Module} {targetHost : HostEnv World}
    {Q : Assertion World} {initial : Store World} {rest : Program} :
    (words : List Value) → (index : Nat) → (locals : Locals) →
    (∀ i (bound : i < words.length), locals.get (index + i) = some words[i]) →
    wp target rest Q initial { locals with values := words.reverse ++ locals.values } targetHost →
    wp target ((List.range' index words.length).map Instruction.localGet ++ rest)
      Q initial locals targetHost
  | [], _, locals, _, next => by
      simpa only [List.reverse_nil, List.nil_append, List.length_nil, List.range'_zero,
        List.map_nil] using next
  | word :: words, index, locals, get, next => by
      have head : locals.get index = some word := get 0 (by simp)
      simp only [List.length_cons, List.range'_succ, List.map_cons, List.cons_append,
        wp_localGet_cons, head]
      refine wp_wrapper_localGets words (index + 1) _ (fun i bound => ?_) ?_
      · rw [Locals.get_values, show index + 1 + i = index + (i + 1) by omega]
        exact get (i + 1) (by simp; omega)
      · simpa using next

theorem wp_wrapper_constI64s {World : Type} {target : Wasm.Module} {targetHost : HostEnv World}
    {Q : Assertion World} {initial : Store World} {rest : Program} :
    (constants : List UInt64) → (locals : Locals) →
    wp target rest Q initial
      { locals with values := (constants.map Value.i64).reverse ++ locals.values } targetHost →
    wp target (constants.map Instruction.constI64 ++ rest) Q initial locals targetHost
  | [], locals, next => by simpa using next
  | constant :: constants, locals, next => by
      simp only [List.map_cons, List.cons_append, wp_constI64_cons]
      refine wp_wrapper_constI64s constants _ ?_
      simpa using next

theorem wp_injected_arguments {World : Type} {target : Wasm.Module} {targetHost : HostEnv World}
    {Q : Assertion World} {initial : Store World} {rest : Program} {locals : Locals}
    (tables : List UInt64) (words : List Value) (parameters : locals.params = words)
    (next : wp target rest Q initial
      { locals with values := (.i64 0 :: (tables.map Value.i64 ++ words)).reverse ++ locals.values }
      targetHost) :
    wp target ([.constI64 0] ++ tables.map Instruction.constI64 ++
      (List.range words.length).map Instruction.localGet ++ rest) Q initial locals targetHost := by
  simp only [List.cons_append, List.nil_append, wp_constI64_cons, List.append_assoc,
    List.range_eq_range']
  refine wp_wrapper_constI64s tables _ ?_
  refine wp_wrapper_localGets words 0 _ (fun i bound => ?_) ?_
  · simp [Locals.get, parameters, bound]
  · simpa [List.reverse_append, List.append_assoc] using next

end Verified.Wasi
