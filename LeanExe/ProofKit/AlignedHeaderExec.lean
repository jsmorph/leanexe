import LeanExe.ProofKit.FixedArrayHeaderExec
import LeanExe.ProofKit.AlignedExec

/-!
A port of `FixedArrayHeaderExec.lean` to `wpA`: the six stores of a fresh block's header, which
`alloc` writes at the payload pointer minus 48, 40, 32, 24, 16, and 8.  When the block's base,
the payload pointer minus 48, is a multiple of 8, every store is aligned.  The proofs are those
of `writeConst_spec`, `writeLocal_spec`, and `program_spec` with `wpA` rules for the `wp` rules,
one premise of alignment, and the alignment conjunct of each store.
-/

namespace LeanExe.ProofKit.FixedArrayHeader
open Wasm LeanExe.ProofKit.Memory LeanExe.ProofKit.Allocation LeanExe.ProofKit

theorem writeConst_specA (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal : Nat)
    (pointer offset value : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hBound : (pointer - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAligned : (pointer - offset).toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q
      { store with mem := store.mem.write64 (pointer - offset).toUInt32 value } frame env) :
    wpA module_ ([.localGet pointerLocal, .constI64 offset, .subI64, .wrapI64,
      .constI64 value, .store64 0] ++ rest) Q store frame env := by
  have hEmpty : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [List.cons_append, List.nil_append, wpA_localGet_cons, wpA_constI64_cons,
    wpA_subI64_cons, wpA_wrapI64_cons, wpA_store64_cons,
    hPointer, hValues, Nat.reducePow, ← toUInt32_eq_ofNat, UInt32.toNat_zero,
    Nat.add_zero, UInt32.add_zero, Nat.not_lt.mpr hBound, reduceIte]
  exact ⟨UInt64.toUInt32_mod8 hAligned, by simpa only [hEmpty] using hNext⟩

theorem writeLocal_specA (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal valueLocal : Nat)
    (pointer offset value : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hBound : (pointer - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (hAligned : (pointer - offset).toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q
      { store with mem := store.mem.write64 (pointer - offset).toUInt32 value } frame env) :
    wpA module_ ([.localGet pointerLocal, .constI64 offset, .subI64, .wrapI64,
      .localGet valueLocal, .store64 0] ++ rest) Q store frame env := by
  have hEmpty : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [List.cons_append, List.nil_append, wpA_localGet_cons, wpA_constI64_cons,
    wpA_subI64_cons, wpA_wrapI64_cons, wpA_store64_cons, Frame.withValues_get,
    hPointer, hValue, hValues, Nat.reducePow, ← toUInt32_eq_ofNat, UInt32.toNat_zero,
    Nat.add_zero, UInt32.add_zero, Nat.not_lt.mpr hBound, reduceIte]
  exact ⟨UInt64.toUInt32_mod8 hAligned, by simpa only [hEmpty] using hNext⟩

/-- The six header stores of a block whose base is a multiple of 8. -/
theorem program_specA (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal capacityLocal : Nat)
    (base capacity stride : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 (base + 48)))
    (hCapacity : frame.get capacityLocal = some (.i64 capacity))
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hFit : base.toNat + 48 ≤ store.mem.pages * 65536)
    (hBase : base.toNat % 8 = 0)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wpA module_ rest Q
      { store with mem := fixedArrayHeaderMem store.mem base capacity stride } frame env) :
    wpA module_ (program pointerLocal capacityLocal stride ++ rest) Q store frame env := by
  obtain ⟨h40, h32, h24, h16, h8⟩ := headerOffsets base hFit32
  have h48 : (base + 48 - 48).toNat = base.toNat := by
    rw [root_sub_toNat base 48 hFit32 (by decide)]
    rfl
  have hBound (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (base + 48 - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [toUInt32_toNat, root_sub_toNat base offset hFit32 hHigh]
    omega
  have hAl (offset : UInt64) (hOffset : offset.toNat % 8 = 0) :
      (base + 48 - offset).toNat % 8 = 0 :=
    UInt64.sub_mod8 (UInt64.add_mod8 hBase rfl) hOffset
  unfold program
  apply writeConst_specA module_ env store frame pointerLocal (base + 48) 48 _
    hValues hPointer (hBound 48 (by decide) (by decide)) (hAl 48 rfl)
  refine writeConst_specA module_ env _ frame pointerLocal (base + 48) 40 _
    hValues hPointer ?_ (hAl 40 rfl) _ _ ?_
  · exact hBound 40 (by decide) (by decide)
  refine writeLocal_specA module_ env _ frame pointerLocal capacityLocal (base + 48) 32 capacity
    hValues hPointer hCapacity ?_ (hAl 32 rfl) _ _ ?_
  · exact hBound 32 (by decide) (by decide)
  refine writeConst_specA module_ env _ frame pointerLocal (base + 48) 24 _
    hValues hPointer ?_ (hAl 24 rfl) _ _ ?_
  · exact hBound 24 (by decide) (by decide)
  refine writeConst_specA module_ env _ frame pointerLocal (base + 48) 16 _
    hValues hPointer ?_ (hAl 16 rfl) _ _ ?_
  · exact hBound 16 (by decide) (by decide)
  refine writeConst_specA module_ env _ frame pointerLocal (base + 48) 8 _
    hValues hPointer ?_ (hAl 8 rfl) _ _ ?_
  · exact hBound 8 (by decide) (by decide)
  simpa only [fixedArrayHeaderMem, toUInt32_eq_ofNat, h48, h40, h32, h24, h16, h8]
    using hNext

end LeanExe.ProofKit.FixedArrayHeader
