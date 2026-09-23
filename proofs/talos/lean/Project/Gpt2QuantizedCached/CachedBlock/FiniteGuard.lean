import Project.Gpt2QuantizedCached.CachedBlock.FiniteTest

namespace Project.Gpt2QuantizedCached.CachedBlock
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

def finiteBranchPost (env : HostEnv Unit) (rest : Program) (Q : Assertion Unit) : Assertion Unit :=
  fun cont => match cont with
    | .Fallthrough store frame =>
      wp «module» rest Q store { frame with values := [] } env
    | .Break 0 store frame =>
      wp «module» rest Q store { frame with values := [] } env
    | .Break (k + 1) store frame => Q (.Break k store frame)
    | other => Q other

theorem finiteGuard_spec (env : HostEnv Unit) (initial : Store Unit)
    (owner ptr : UInt64) (input : ByteArray) (count source : Nat)
    (hInput : ByteArrayAt initial.mem ptr.toNat input) (hExtent : count * 4 ≤ input.size)
    (hSource : source = 13 ∨ source = 51 ∨ source = 102 ∨ source = 135)
    (frame : Locals) (hParams : frame.params.length = 11)
    (hLength : frame.locals.length = 193) (hValues : frame.values = [])
    (hOwner : frame.locals[source]? = some (.i64 owner))
    (hPtr : frame.locals[source + 1]? = some (.i64 ptr))
    (hBytes : frame.locals[source + 2]? = some (.i64 (UInt64.ofNat input.size)))
    (hTyped : I64Values frame.locals) (Q : Assertion Unit) (failure success rest : Program)
    (hNext : ∀ result, result.params = frame.params → result.locals.length = 193 →
      I64Values result.locals → result.locals.take (source + 3) = frame.locals.take (source + 3) →
      result.values = [] →
      wp «module» (if finiteWords input 0 count then success else failure)
        (fun cont => match cont with
          | .Fallthrough final after => wp «module» rest Q final { after with values := [] } env
          | .Break 0 final after => wp «module» rest Q final { after with values := [] } env
          | .Break (k + 1) final after => Q (.Break k final after)
          | other => Q other) initial result env) :
    wp «module» (finiteTestCode source count ++ [.iff 0 0 failure success] ++ rest) Q initial frame env := by
  simp only [List.append_assoc]
  apply finiteTest_spec env initial owner ptr input count source hInput hExtent hSource
    frame hParams hLength hValues hOwner hPtr hBytes hTyped
  intro result hResultParams hResultLength hResultTyped hResultPrefix hResultValues
  simp only [List.cons_append, List.nil_append, wp_iff_control_types]
  refine wp_iff_cons hResultValues ?_
  have hRun := hNext { result with values := [] } hResultParams hResultLength hResultTyped hResultPrefix rfl
  cases hFinite : finiteWords input 0 count
  · rw [ite_eq_left (by simp [hFinite])]
    simp only [hFinite, Bool.false_eq_true, ite_false] at hRun
    convert hRun using 2
    rename_i cont
    cases cont <;> try rfl
    rename_i k _ _
    cases k <;> rfl
  · rw [ite_eq_right (by simp [hFinite])]
    simp only [hFinite, ite_true] at hRun
    convert hRun using 2
    rename_i cont
    cases cont <;> try rfl
    rename_i k _ _
    cases k <;> rfl

#print axioms finiteGuard_spec
end Project.Gpt2QuantizedCached.CachedBlock
