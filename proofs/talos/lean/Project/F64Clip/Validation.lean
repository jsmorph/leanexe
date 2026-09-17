import Project.F64Clip.Scan

namespace Project.F64Clip.Spec
open Wasm Project.ProofKit Project.ProofKit.F64Order

theorem accepted_exact (env : HostEnv Unit) (initial : Store Unit)
    (count bound unused ptr : UInt64) (w : Array UInt64) (hInput : UInt64Array.At initial ptr w) :
    TerminatesWith env Project.F64Clip.module 3 initial [.i64 ptr, .i64 unused, .i64 bound, .i64 count]
      (fun final values => final = initial ∧ values = [.i64 (if accepted count.toNat bound w then 1 else 0)]) := by
  have hLengthEq : UInt64.ofNat w.size = count ↔ w.size = count.toNat := by
    constructor
    · intro h
      have hh := congrArg UInt64.toNat h
      simpa only [UInt64.toNat_ofNat_of_lt' hInput.size_lt] using hh
    · intro h
      rw [h, UInt64.ofNat_toNat]
  refine TerminatesWith.of_wp_entry_for (f := func3Def) rfl ?_ (by decide)
  change wp Project.F64Clip.module func3 _ initial
    (func3Def.toLocals [.i64 count, .i64 bound, .i64 unused, .i64 ptr]) env
  unfold func3
  wp_fixed_frame [func3Def]
  simp [hInput.pointerAddress_eq, hInput.lengthRead, hInput.generatedLengthBound]
  by_cases hs : UInt64.ofNat w.size = count
  · subst count
    let count := UInt64.ofNat w.size
    cases hb : validBound bound
    all_goals
      repeat first
        | wp_fixed_frame [func3Def, hb, hInput.pointerAddress_eq, hInput.lengthRead]
        | (try simp only [Wasm.wp_iff_control_types]
           refine wp_iff_cons rfl ?_
           simp)
        | (refine wp_call_tw (validBound_exact env initial bound) ?_
           rintro final values ⟨hFinal, rfl⟩
           subst final)
    · simp [accepted, hb]
    · simp [hInput.generatedLengthBound]
      refine wp_iff_cons rfl ?_
      simp only [ne_eq, not_true_eq_false, ite_false]
      wp_fixed_frame [func3Def]
      change wp Project.F64Clip.module
        ([.block 0 0 [.loop 0 0 scanBody]] ++ _) _ initial
        (scanFrame count bound unused ptr w.size 0 0 1) env
      refine BlockLoop.program_spec Project.F64Clip.module env initial _ scanBody
        (scanInv initial count bound unused ptr w) (scanDone initial count bound unused ptr w)
        (scanMeasure w) ?_ ?_ ?_ (scan_step env initial count bound unused ptr w hInput) _ _ ?_
      · rintro st frame ⟨_, index, last, _, rfl, _⟩
        rfl
      · rintro st frame ⟨_, index, last, rfl⟩
        rfl
      · exact ⟨rfl, 0, 0, Nat.zero_le _, rfl, by simp⟩
      · rintro st frame ⟨hStore, index, last, rfl⟩
        subst st
        cases ha : w.all (fun x => finiteBits x)
        all_goals
          repeat first
            | wp_fixed_frame [scanFrame, ha]
            | (try simp only [Wasm.wp_iff_control_types]
               refine wp_iff_cons rfl ?_
               simp)
        all_goals simp [accepted, hb, ha, Nat.mod_eq_of_lt hInput.size_lt]
  · have hSize : w.size ≠ count.toNat := fun hh => hs (hLengthEq.mpr hh)
    repeat first
      | wp_fixed_frame [func3Def, hs]
      | (try simp only [Wasm.wp_iff_control_types]
         refine wp_iff_cons rfl ?_
         simp)
    simp [accepted, hSize]

#print axioms accepted_exact
end Project.F64Clip.Spec
