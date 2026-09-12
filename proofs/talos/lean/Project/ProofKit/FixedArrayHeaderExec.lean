import Project.ProofKit.FixedArrayHeader
import Project.ProofKit.Frame
import Interpreter.Wasm.Wp.Tactic

namespace Project.ProofKit.FixedArrayHeader
open Wasm Project.Clob Project.ProofKit.Memory Project.ProofKit.Allocation

theorem writeConst_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal : Nat)
    (pointer offset value : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hBound : (pointer - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with mem := store.mem.write64 (pointer - offset).toUInt32 value } frame env) :
    wp module_ ([.localGet pointerLocal, .constI64 offset, .subI64, .wrapI64,
      .constI64 value, .store64 0] ++ rest) Q store frame env := by
  have hEmpty : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, wp_constI64_cons,
    wp_subI64_cons, wp_wrapI64_cons, wp_store64_cons,
    hPointer, hValues, Nat.reducePow, ← toUInt32_eq_ofNat, UInt32.toNat_zero,
    Nat.add_zero, UInt32.add_zero, Nat.not_lt.mpr hBound, reduceIte]
  simpa only [hEmpty] using hNext

theorem writeLocal_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal valueLocal : Nat)
    (pointer offset value : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 pointer))
    (hValue : frame.get valueLocal = some (.i64 value))
    (hBound : (pointer - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with mem := store.mem.write64 (pointer - offset).toUInt32 value } frame env) :
    wp module_ ([.localGet pointerLocal, .constI64 offset, .subI64, .wrapI64,
      .localGet valueLocal, .store64 0] ++ rest) Q store frame env := by
  have hEmpty : { frame with values := [] } = frame := Frame.ext _ _ rfl rfl hValues.symm
  simp only [List.cons_append, List.nil_append, wp_localGet_cons, wp_constI64_cons,
    wp_subI64_cons, wp_wrapI64_cons, wp_store64_cons, Frame.withValues_get,
    hPointer, hValue, hValues, Nat.reducePow, ← toUInt32_eq_ofNat, UInt32.toNat_zero,
    Nat.add_zero, UInt32.add_zero, Nat.not_lt.mpr hBound, reduceIte]
  simpa only [hEmpty] using hNext

def program (pointerLocal capacityLocal : Nat) (stride : UInt64) : Wasm.Program :=
  [.localGet pointerLocal, .constI64 48, .subI64, .wrapI64,
    .constI64 5501223100278326855, .store64 0,
   .localGet pointerLocal, .constI64 40, .subI64, .wrapI64,
    .constI64 1, .store64 0,
   .localGet pointerLocal, .constI64 32, .subI64, .wrapI64,
    .localGet capacityLocal, .store64 0,
   .localGet pointerLocal, .constI64 24, .subI64, .wrapI64,
    .constI64 2, .store64 0,
   .localGet pointerLocal, .constI64 16, .subI64, .wrapI64,
    .constI64 stride, .store64 0,
   .localGet pointerLocal, .constI64 8, .subI64, .wrapI64,
    .constI64 0, .store64 0]

theorem program_spec (module_ : Wasm.Module) (env : HostEnv Unit)
    (store : Store Unit) (frame : Locals) (pointerLocal capacityLocal : Nat)
    (base capacity stride : UInt64) (hValues : frame.values = [])
    (hPointer : frame.get pointerLocal = some (.i64 (base + 48)))
    (hCapacity : frame.get capacityLocal = some (.i64 capacity))
    (hFit32 : base.toNat + 48 ≤ 4294967296)
    (hFit : base.toNat + 48 ≤ store.mem.pages * 65536)
    (Q : Assertion Unit) (rest : Wasm.Program)
    (hNext : wp module_ rest Q
      { store with mem := fixedArrayHeaderMem store.mem base capacity stride } frame env) :
    wp module_ (program pointerLocal capacityLocal stride ++ rest) Q store frame env := by
  obtain ⟨h40, h32, h24, h16, h8⟩ := headerOffsets base hFit32
  have h48 : (base + 48 - 48).toNat = base.toNat := by
    rw [root_sub_toNat base 48 hFit32 (by decide)]
    rfl
  have hBound (offset : UInt64) (hLow : 8 ≤ offset.toNat) (hHigh : offset.toNat ≤ 48) :
      (base + 48 - offset).toUInt32.toNat + 8 ≤ store.mem.pages * 65536 := by
    rw [toUInt32_toNat, root_sub_toNat base offset hFit32 hHigh]
    omega
  unfold program
  apply writeConst_spec module_ env store frame pointerLocal (base + 48) 48 _
    hValues hPointer (hBound 48 (by decide) (by decide))
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 40 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 40 (by decide) (by decide)
  refine writeLocal_spec module_ env _ frame pointerLocal capacityLocal (base + 48) 32 capacity
    hValues hPointer hCapacity ?_ _ _ ?_
  · exact hBound 32 (by decide) (by decide)
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 24 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 24 (by decide) (by decide)
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 16 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 16 (by decide) (by decide)
  refine writeConst_spec module_ env _ frame pointerLocal (base + 48) 8 _
    hValues hPointer ?_ _ _ ?_
  · exact hBound 8 (by decide) (by decide)
  simpa only [fixedArrayHeaderMem, toUInt32_eq_ofNat, h48, h40, h32, h24, h16, h8]
    using hNext

#print axioms writeConst_spec
#print axioms writeLocal_spec
#print axioms program_spec

end Project.ProofKit.FixedArrayHeader
