import Project.TinyGpt2Checked.EntryAccept
import Project.TinyGpt2.Checked

namespace Project.TinyGpt2Checked.Spec
open Wasm Project.ProofKit Project.TinyGpt2

theorem inferChecked_export : module.findExport "inferChecked" = some 85 := rfl

theorem inferChecked_exact (env : HostEnv Unit) (initial : Store Unit)
    (pointer bound t0 t1 t2 t3 base : UInt64) (weights : Array UInt64)
    (allocations retains releases frees : UInt64)
    (hGlobals : initial.globals.globals =
      [.i64 base, .i64 0, .i64 allocations, .i64 retains, .i64 releases, .i64 frees])
    (hInput : UInt64Array.At initial pointer weights)
    (hBefore : pointer.toNat+8*(weights.size+1) ≤ base.toNat)
    (hFit : base.toNat+48+8*(weights.size+1)+277560 < 4294967296)
    (hMemory : base.toNat+48+8*(weights.size+1)+277560 ≤ initial.mem.pages*65536)
    (hPages : initial.mem.pages ≤ 65536)
    (hCap : initial.mem.pages ≤ initial.memoryCap module 0) :
    TerminatesWith env module 85 initial
      [.i64 t3, .i64 t2, .i64 t1, .i64 t0, .i64 bound, .i64 pointer]
      (fun final values => ∃ root : UInt64, values = [.i64 root] ∧
        UInt64Array.At final root (inferChecked weights bound t0 t1 t2 t3) ∧
        UInt64Array.At final pointer weights ∧ final.mem.pages = initial.mem.pages ∧
        (∀ address : Nat, address < base.toNat → final.mem.bytes address = initial.mem.bytes address) ∧
        final = { initial with mem := final.mem, globals := final.globals }) := by
  refine TerminatesWith.of_wp_entry_for (f := func85Def) rfl ?_ (by decide)
  change wp module func85 _ initial (checkedFrame pointer bound t0 t1 t2 t3) env
  apply token_guard_spec
  by_cases ht : t0 < 256 ∧ t1 < 256 ∧ t2 < 256 ∧ t3 < 256
  · simp only [ht]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq]
    apply token_accept_spec env initial pointer bound t0 t1 t2 t3 base weights
      allocations retains releases frees hGlobals hInput hBefore hFit hMemory hPages hCap
      ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 _ []
    rintro final frame ⟨root, hRoot, hValues, hOutput, hInput', hPages', hBytes, hStore⟩
    have hModel : inferChecked weights bound t0 t1 t2 t3 =
        checkedPreparedOutput weights bound t0 t1 t2 t3 := by
      simp [inferChecked, checkedPreparedOutput, Layout.size, ht.1, ht.2.1, ht.2.2.1, ht.2.2.2]
    simp only [Locals.get] at hRoot
    simp [wp_simp, hRoot, func85Def, Function.numParams, hModel, hOutput,
      hInput', hPages']
    exact ⟨hBytes, hStore⟩
  · simp only [ht, ite_false]
    refine wp_iff_cons rfl ?_
    simp only [ne_eq, not_true_eq_false, ite_false]
    apply token_reject_spec env initial pointer bound t0 t1 t2 t3 base weights
      allocations retains releases frees hGlobals hInput hBefore (by omega) (by omega) hPages hCap _ []
    rintro final frame ⟨root, hRoot, hValues, hOutput, hInput', hPages', hBytes, hStore⟩
    have hModel : inferChecked weights bound t0 t1 t2 t3 = #[] := by
      simp [inferChecked, Bool.and_eq_true, decide_eq_true_eq, and_assoc, ht]
    simp only [Locals.get] at hRoot
    simp [wp_simp, hRoot, func85Def, Function.numParams, hModel, hOutput,
      hInput', hPages']
    exact ⟨hBytes, hStore⟩

#print axioms inferChecked_exact
end Project.TinyGpt2Checked.Spec
