import Project.Gpt2QuantizedCached.Entry.FiniteTest
import Project.Gpt2QuantizedCached.Entry.StateTransfer

namespace Project.Gpt2QuantizedCached.Entry
open Wasm Project.ProofKit PackedMemory PackedFloatFrame LeanExe.Models.Gpt2.Quantized

theorem boolBranch_spec (env : HostEnv Unit) (store : Store Unit) (frame : Locals) (rejected : Bool)
    (hValues : frame.values = [.i32 (if rejected then 1 else 0)])
    (Q : Assertion Unit) (failure success rest : Program)
    (hNext : wp «module» (if rejected then failure else success)
      (PackedReleaseFilter.afterAction «module» env rest Q) store { frame with values := [] } env) :
    wp «module» ([.iff 0 0 failure success] ++ rest) Q store frame env := by
  simp only [List.cons_append, List.nil_append]
  refine wp_iff_cons hValues ?_
  cases rejected
  all_goals
    first | rw [ite_eq_left (by decide)] | rw [ite_eq_right (by decide)]
    simp only [Bool.false_eq_true, ite_true, ite_false, List.take_zero, List.drop_zero, List.nil_append] at hNext ⊢
    apply wp.imp hNext
    intro cont hCont
    cases cont with
    | Break level next result => cases level <;> exact hCont
    | _ => exact hCont

theorem normalizedGuard_spec (env : HostEnv Unit) (initial : Store Unit)
    (params : List Value) (hidden cache normalized : UInt64) (cacheSize : Nat)
    (input : ByteArray) (frame : Locals)
    (hParams : params.length = 8) (hInput : ByteArrayAt initial.mem normalized.toNat input)
    (hSize : input.size = 3072)
    (hState : NormalizedState params hidden cache normalized cacheSize frame)
    (Q : Assertion Unit) (failure success rest : Program)
    (hNext : ∀ result, NormalizedState params hidden cache normalized cacheSize result →
      wp «module» (if finiteWords input 0 768 then success else failure)
        (PackedReleaseFilter.afterAction «module» env rest Q) initial result env) :
    wp «module» (finiteTestCode 42 45 768 ++ ReadOnlyDisjunction.negateProgram ++
      ReadOnlyDisjunction.canonicalProgram ++ [.iff 0 0 failure success] ++ rest) Q initial frame env := by
  simp only [List.append_assoc]
  apply finiteTest_spec env initial normalized normalized input 768 42 45 hInput (by rw [hSize])
    (Or.inl ⟨rfl, rfl⟩) frame (by rw [hState.paramsEq, hParams]) hState.length hState.values
    hState.normalizedOwner hState.normalizedPtr (by simpa only [hSize, Nat.reduceAdd, show UInt64.ofNat 3072 = 3072 from rfl] using hState.normalizedSize) hState.typed
  intro result hResultParams hResultLength hResultTyped hPrefix hValues
  apply ReadOnlyDisjunction.negate_spec _ _ _ _ _ hValues
  apply ReadOnlyDisjunction.canonical_spec _ _ _ _ _ rfl
  apply boolBranch_spec env initial _ (!finiteWords input 0 768) rfl
  have hFinalState := hState.transfer (after := { result with values := [] })
    hResultParams hResultLength rfl hResultTyped hPrefix (by decide)
  cases hFinite : finiteWords input 0 768 <;> simpa only [hFinite, Bool.not_false, Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true] using hNext _ hFinalState

#print axioms boolBranch_spec
#print axioms normalizedGuard_spec
end Project.Gpt2QuantizedCached.Entry
