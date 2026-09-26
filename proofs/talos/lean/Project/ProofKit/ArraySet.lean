import Project.ProofKit.ArrayPrefix
import Project.ProofKit.FixedArrayCopy
import Project.ProofKit.Frame

namespace Project.ProofKit.UInt64Array

open Wasm Memory FixedArrayCopy

theorem At.writeElement_set {store : Store Unit} {ptr : UInt64} {values : Array UInt64}
    (represented : At store ptr values) (index : Nat) (value : UInt64) (inside : index < values.size) :
    At (writeElement store ptr index value) ptr (values.set! index value) := by
  have size : (values.set! index value).size = values.size := by simp
  refine ⟨by simpa only [size] using represented.1, by simpa only [size, writeElement_pages] using represented.2.1, ?_, ?_⟩
  · rw [size]
    apply (read64_write64_disjoint store.mem _ _ ptr.toUInt32 ?_).trans represented.lengthRead
    left
    rw [represented.pointerAddress_toNat, wordAddress_toNat represented.1 (by omega)]
    omega
  · intro j hj
    have oldBound : j < values.size := by omega
    rw [← getElem!_pos (values.set! index value) j hj]
    by_cases equal : j = index
    · subst j
      rw [Array.getElem!_set!_self values index value inside]
      exact read64_write64 ..
    · rw [Array.getElem!_set!_ne values index j value (Ne.symm equal), getElem!_pos values j oldBound]
      apply (read64_write64_disjoint store.mem _ _ _ ?_).trans (represented.elementRead j oldBound)
      change (wordAddress ptr (j + 1)).toNat + 8 ≤ (wordAddress ptr (index + 1)).toNat ∨
        (wordAddress ptr (index + 1)).toNat + 8 ≤ (wordAddress ptr (j + 1)).toNat
      rw [wordAddress_toNat represented.1 (show j + 1 < values.size + 1 by omega),
        wordAddress_toNat represented.1 (show index + 1 < values.size + 1 by omega)]
      omega

def setStoreProgram (targetLocal indexLocal valueLocal : Nat) : Wasm.Program :=
  [.localGet targetLocal, .localGet indexLocal, .constI64 1, .mulI64,
    .constI64 1, .addI64, .constI64 8, .mulI64, .addI64, .wrapI64,
    .localGet valueLocal, .store64 0]

theorem setStoreProgram_spec (targetLocal indexLocal valueLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (store : Store Unit) (frame : Locals)
    (target : UInt64) (input : Array UInt64) (index : Nat) (value : UInt64)
    (hValues : frame.values = []) (hTarget : frame.get targetLocal = some (.i64 target))
    (hIndex : frame.get indexLocal = some (.i64 index.toUInt64)) (hValue : frame.get valueLocal = some (.i64 value))
    (represented : At store target input) (inside : index < input.size)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : wp module_ rest Q (writeElement store target index value) frame env) :
    wp module_ (setStoreProgram targetLocal indexLocal valueLocal ++ rest) Q store frame env := by
  have bound : (wordAddress target (index + 1)).toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [wordAddress_toNat represented.1 (by omega)]
    have := represented.2.1
    omega
  have frameEq : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [setStoreProgram, List.cons_append, List.nil_append, wp_localGet_cons,
    Frame.withValues_get, hTarget, hIndex, hValue, hValues, wp_constI64_cons,
    wp_mulI64_cons, wp_addI64_cons, wp_wrapI64_cons, wp_store64_cons]
  rw [generatedElementAddress]
  simp only [UInt32.add_zero, UInt32.toNat_zero, Nat.add_zero]
  rw [ite_eq_right (by omega)]
  simpa only [writeElement, frameEq] using next

theorem setCopy_spec (sourceLocal targetLocal countLocal indexLocal counterLocal valueLocal : Nat)
    (module_ : Wasm.Module) (env : HostEnv Unit) (initial : Store Unit) (frame : Locals)
    (source target : UInt64) (input : Array UInt64) (index : Nat) (value : UInt64)
    (hCounter : frame.validIndex counterLocal) (hValues : frame.values = [])
    (hSourceNe : sourceLocal ≠ counterLocal) (hTargetNe : targetLocal ≠ counterLocal)
    (hCountNe : countLocal ≠ counterLocal) (hIndexNe : indexLocal ≠ counterLocal) (hValueNe : valueLocal ≠ counterLocal)
    (hSource : frame.get sourceLocal = some (.i64 source)) (hTarget : frame.get targetLocal = some (.i64 target))
    (hCount : frame.get countLocal = some (.i64 input.size.toUInt64))
    (hIndex : frame.get indexLocal = some (.i64 index.toUInt64)) (hValue : frame.get valueLocal = some (.i64 value))
    (hInput : At initial source input) (inside : index < input.size)
    (hFit : target.toNat + 8 * (input.size + 1) ≤ 4294967296)
    (hMemory : target.toNat + 8 * (input.size + 1) ≤ initial.mem.pages * 65536)
    (hHeader : initial.mem.read64 target.toUInt32 = input.size.toUInt64)
    (hSeparate : source.toNat + 8 * (input.size + 1) ≤ target.toNat ∨
      target.toNat + 8 * (input.size + 1) ≤ source.toNat)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (next : ∀ final, WritesRange initial final target.toNat (target.toNat + 8 * (input.size + 1)) →
      At final source input → At final target (input.set! index value) →
      wp module_ rest Q final (counterFrame frame counterLocal input.size hCounter) env) :
    wp module_ (prefixProgram sourceLocal targetLocal countLocal counterLocal ++
      setStoreProgram targetLocal indexLocal valueLocal ++ rest) Q initial frame env := by
  rw [List.append_assoc]
  apply prefixProgram_framed_spec sourceLocal targetLocal countLocal counterLocal module_ env initial frame
    source target input.size input.size input.size hCounter hSourceNe hTargetNe hCountNe hValues hSource hTarget hCount
    (Nat.le_refl _) (Nat.le_refl _) hInput.1 hFit hInput.2.1 hMemory hSeparate
  intro middle pages header _ copied writes
  have represented : At middle target input :=
    ⟨hFit, by simpa only [pages] using hMemory, header.trans hHeader,
      fun j hj => (copied j hj).trans (hInput.elementRead j hj)⟩
  apply setStoreProgram_spec targetLocal indexLocal valueLocal module_ env middle
    (counterFrame frame counterLocal input.size hCounter) target input index value rfl
    ((counterFrame_get_ne _ _ _ _ hCounter hTargetNe).trans hTarget)
    ((counterFrame_get_ne _ _ _ _ hCounter hIndexNe).trans hIndex)
    ((counterFrame_get_ne _ _ _ _ hCounter hValueNe).trans hValue) represented inside
  have total := (writes.mono (by omega) (by omega)).trans (writeElement_frame middle target input.size index value hFit inside)
  exact next _ total (hInput.writesRange total hSeparate) (represented.writeElement_set index value inside)

#print axioms At.writeElement_set
#print axioms setCopy_spec

end Project.ProofKit.UInt64Array
