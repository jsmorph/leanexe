import Verified.Wasi.SysWords
import Verified.Wasi.SysCode
import Verified.LocalFrame

/-! The argument code of a flat call: the test that rejects arguments that do not fit their core
types, and the code that pushes the core arguments, with the buffer's root for the output and the
scratch addresses for the result words. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Runtime

/-- The pointers of a flat call's request: the buffer's root for its output, and the scratch
address `slot`, then `slot + 8`, for its result words. -/
def flatPointers : List Param → UInt32 → Nat → List UInt32
  | [], _, _ => []
  | .output :: params, root, slot => root :: flatPointers params root slot
  | .result32 :: params, root, slot
  | .result64 :: params, root, slot => UInt32.ofNat slot :: flatPointers params root (slot + 8)
  | _ :: params, root, slot => flatPointers params root slot

theorem lowerArgs_length : ∀ (params : List Param) (args : List Arg) (pointers : List UInt32),
    (lowerArgs params args pointers).length = (params.flatMap ABI.paramTypes).length
  | [], _, _ => rfl
  | param :: params, args, pointers => by
    cases param <;>
      simp only [lowerArgs, ABI.paramTypes, List.flatMap_cons, List.length_cons,
        List.length_append, lowerArgs_length params, List.length_nil] <;> omega

theorem inputPlaces_flat : ∀ (params : List Param) (args : List Arg) (pointers : List UInt32),
    params.all Param.flatKind = true → inputPlaces params args pointers = []
  | [], _, _, _ => rfl
  | param :: params, args, pointers, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input | reported | record => simp [Param.flatKind] at kinds
    | word32 | word64 | enum32 | output | result32 | result64 | flags32 | flags64 =>
      simp only [inputPlaces]
      exact inputPlaces_flat _ _ _ kinds.2

theorem uint32_ofNat_toNat (value : UInt64) : UInt32.ofNat value.toNat = value.toUInt32 := by
  apply UInt32.toNat_inj.mp
  simp [UInt64.toNat_toUInt32]

/-- The first argument word and its local, for a parameter that takes an argument. -/
private theorem held_head {s : Locals} {locs : List Nat} {values : List UInt64} {count : Nat}
    (held : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (length : values.length = count + 1) :
    ∃ place value locs' values', s.get place = some (.i64 value) ∧
      List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs' values' ∧
      locs = place :: locs' ∧ values = value :: values' := by
  cases held with
  | nil => simp at length
  | cons head tail => exact ⟨_, _, _, _, head, tail, rfl, rfl⟩

private theorem held_values {s : Locals} {locs : List Nat} {values : List UInt64}
    (held : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (stack : List Value) :
    List.Forall₂ (fun place value =>
      ({ s with values := stack } : Locals).get place = some (.i64 value)) locs values := by
  simpa only [Locals.get_values] using held

/-- The flags test leaves 28 when the word in `place` has a bit outside `mask`, and otherwise the
errno that the code after it leaves. -/
theorem wp_flags_reject {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {mask place : Nat} {value accepted : UInt64} {code rest : Program} {s : Locals}
    {Q : Assertion α}
    (hPlace : s.get place = some (.i64 value))
    (hCode : value &&& ~~~(UInt64.ofNat mask) = 0 → ∀ (rest' : Program) (Q' : Assertion α),
      wp m rest' Q' st { s with values := .i64 accepted :: s.values } env →
      wp m (code ++ rest') Q' st s env)
    (h : wp m rest Q st
      { s with values := .i64 (if value &&& ~~~(UInt64.ofNat mask) = 0 then accepted else 28) ::
        s.values } env) :
    wp m (flagsRejectCode mask place code ++ rest) Q st s env := by
  simp only [flagsRejectCode, List.cons_append, wp_localGet_cons, hPlace, wp_constI64_cons,
    wp_andI64_cons, wp_eqzI64_cons, wp_iff_control_types]
  refine wp_iff_cons rfl ?_
  by_cases ok : value &&& ~~~(UInt64.ofNat mask) = 0
  · rw [ite_eq_left (by simp [ok])]
    rw [← List.append_nil code]
    refine hCode ok [] _ ?_
    simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
      List.drop_zero]
    simpa only [ok, ite_true] using h
  · rw [ite_eq_right (by simp [ok])]
    simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
      List.cons_append, List.nil_append, List.drop_zero]
    simpa only [ok, ite_false] using h

/-- The test of the arguments leaves the errno that rejects them, or 0. -/
theorem wp_sys_reject {α : Type} {m : Module} {st : Store α} {env : HostEnv α} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64) (s : Locals)
      (rest : Program) (Q : Assertion α),
    params.all Param.flatKind = true →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = params.countP Param.takesArg →
    wp m rest Q st
      { s with values := .i64 (rejectArgs params (flatArgs params values)) :: s.values } env →
    wp m (sysRejectCode params locs ++ rest) Q st s env
  | [], _, _, s, rest, Q, _, _, _, h => by
    simpa only [sysRejectCode, rejectArgs, List.cons_append, List.nil_append,
      wp_constI64_cons] using h
  | param :: params, locs, values, s, rest, Q, kinds, held, count, h => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input | reported | record => simp [Param.flatKind] at kinds
    | flags64 mask =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg)
          (by simpa [Param.takesArg, List.countP_cons] using count)
      simp only [sysRejectCode]
      refine wp_flags_reject hPlace (fun _ rest' Q' next => wp_sys_reject params locs' values' s
        rest' Q' kinds.2 held' (by simpa [Param.takesArg, List.countP_cons] using count) next) ?_
      by_cases ok : value &&& ~~~(UInt64.ofNat mask) = 0 <;>
        simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value, ok] using h
    | flags32 mask =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg)
          (by simpa [Param.takesArg, List.countP_cons] using count)
      simp only [sysRejectCode, List.cons_append, wp_localGet_cons, hPlace, wp_constI64_cons,
        wp_geUI64_cons, wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      by_cases large : (4294967296 : UInt64) ≤ value
      · rw [ite_eq_left (by simp [large])]
        simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
          List.cons_append, List.nil_append, List.drop_zero]
        have large' : ¬value.toNat < 4294967296 := by
          rw [UInt64.le_iff_toNat_le] at large
          simp only [UInt64.reduceToNat] at large
          omega
        simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value, large'] using h
      · rw [ite_eq_right (by simp [large])]
        have small : value.toNat < 4294967296 := by
          rw [UInt64.le_iff_toNat_le] at large
          simp only [UInt64.reduceToNat] at large
          omega
        rw [← List.append_nil (flagsRejectCode mask place (sysRejectCode params locs'))]
        refine wp_flags_reject (by simpa only [Locals.get_values] using hPlace)
          (fun _ rest' Q' next => wp_sys_reject params locs' values' _ rest' Q' kinds.2
            (held_values held' _) (by simpa [Param.takesArg, List.countP_cons] using count)
            next) ?_
        simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
          List.nil_append, List.drop_zero]
        by_cases ok : value &&& ~~~(UInt64.ofNat mask) = 0 <;>
          simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value, small, ok] using h
    | result32 | result64 =>
      simp only [sysRejectCode]
      refine wp_sys_reject params locs values s rest Q kinds.2 held
        (by simpa [Param.takesArg, List.countP_cons] using count) ?_
      simpa only [rejectArgs, flatArgs, Param.takesArg, Bool.false_eq_true, ite_false] using h
    | word64 =>
      obtain ⟨place, value, locs', values', _, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg) (by simpa [Param.takesArg, List.countP_cons] using count)
      simp only [sysRejectCode]
      refine wp_sys_reject params locs' values' s rest Q kinds.2 held'
        (by simpa [Param.takesArg, List.countP_cons] using count) ?_
      simpa only [rejectArgs, flatArgs, Param.takesArg, Param.reject, ite_true,
        List.headD_cons, List.tail_cons] using h
    | word32 | output | enum32 bound =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg) (by simpa [Param.takesArg, List.countP_cons] using count)
      have bound' : ∀ {bound : Nat}, Param.flatKind (.enum32 bound) = true →
          (UInt64.ofNat bound).toNat = bound := by
        intro bound flat
        simp only [Param.flatKind, decide_eq_true_eq] at flat
        exact UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
      simp only [sysRejectCode, List.cons_append, wp_localGet_cons, hPlace, wp_constI64_cons,
        wp_geUI64_cons, wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      first
        | (by_cases large : (4294967296 : UInt64) ≤ value
           · rw [ite_eq_left (by simp [large])]
             simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
               List.cons_append, List.nil_append, List.drop_zero]
             have large' : ¬value.toNat < 4294967296 := by
               rw [UInt64.le_iff_toNat_le] at large
               simp only [UInt64.reduceToNat] at large
               omega
             simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value, Arg.capacity,
               large'] using h
           · rw [ite_eq_right (by simp [large])]
             have small : value.toNat < 4294967296 := by
               rw [UInt64.le_iff_toNat_le] at large
               simp only [UInt64.reduceToNat] at large
               omega
             rw [← List.append_nil (sysRejectCode params locs')]
             refine wp_sys_reject params locs' values' _ [] _ kinds.2 (held_values held' _)
               (by simpa [Param.takesArg, List.countP_cons] using count) ?_
             simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
               List.nil_append, List.drop_zero]
             simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value,
               Arg.capacity, small] using h)
        | (have bound'' := bound' kinds.1
           by_cases large : UInt64.ofNat bound ≤ value
           · rw [ite_eq_left (by simp [large])]
             simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
               List.cons_append, List.nil_append, List.drop_zero]
             have large' : ¬value.toNat < bound := by
               rw [UInt64.le_iff_toNat_le, bound''] at large
               omega
             simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value,
               large'] using h
           · rw [ite_eq_right (by simp [large])]
             have small : value.toNat < bound := by
               rw [UInt64.le_iff_toNat_le, bound''] at large
               omega
             rw [← List.append_nil (sysRejectCode params locs')]
             refine wp_sys_reject params locs' values' _ [] _ kinds.2 (held_values held' _)
               (by simpa [Param.takesArg, List.countP_cons] using count) ?_
             simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
               List.nil_append, List.drop_zero]
             simpa [rejectArgs, flatArgs, Param.takesArg, Param.reject, Arg.value,
               small] using h)

/-- The argument code pushes the core arguments of the request whose pointers are the buffer's
root and the scratch addresses from `slot`. -/
theorem wp_sys_lower {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {rootLocal : Nat} {root : UInt64} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64) (slot : Nat) (s : Locals)
      (rest : Program) (Q : Assertion α),
    params.all Param.flatKind = true →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = params.countP Param.takesArg →
    s.get rootLocal = some (.i64 root) →
    wp m rest Q st { s with values :=
      (lowerArgs params (flatArgs params values) (flatPointers params root.toUInt32 slot)).reverse ++
        s.values } env →
    wp m (sysLowerCode params locs rootLocal slot ++ rest) Q st s env
  | [], _, _, _, s, rest, Q, _, _, _, _, h => by
    simpa only [sysLowerCode, lowerArgs, List.reverse_nil, List.nil_append] using h
  | param :: params, locs, values, slot, s, rest, Q, kinds, held, count, hRoot, h => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input | reported | record => simp [Param.flatKind] at kinds
    | result32 | result64 =>
      simp only [sysLowerCode, List.cons_append, List.nil_append, wp_const_cons]
      refine wp_sys_lower params locs values (slot + 8) _ rest Q kinds.2 (held_values held _)
        (by simpa [Param.takesArg, List.countP_cons] using count) (by simpa only [Locals.get_values] using hRoot) ?_
      simpa only [lowerArgs, flatArgs, flatPointers, List.reverse_cons, List.append_assoc,
        List.headD_cons, List.tail_cons, List.cons_append, List.nil_append] using h
    | word64 | flags64 =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg) (by simpa [Param.takesArg, List.countP_cons] using count)
      simp only [sysLowerCode, List.cons_append, List.nil_append, wp_localGet_cons, hPlace]
      refine wp_sys_lower params locs' values' slot _ rest Q kinds.2 (held_values held' _)
        (by simpa [Param.takesArg, List.countP_cons] using count) (by simpa only [Locals.get_values] using hRoot) ?_
      simpa only [lowerArgs, flatArgs, flatPointers, List.reverse_cons, List.append_assoc,
        List.head?_cons, Option.map_some, Option.getD_some, Arg.value, List.tail_cons,
        List.headD_cons, List.cons_append, List.nil_append] using h
    | word32 | enum32 | flags32 =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg) (by simpa [Param.takesArg, List.countP_cons] using count)
      simp only [sysLowerCode, List.cons_append, List.nil_append, wp_localGet_cons, hPlace,
        wp_wrapI64_cons, wrap_toUInt32]
      refine wp_sys_lower params locs' values' slot _ rest Q kinds.2 (held_values held' _)
        (by simpa [Param.takesArg, List.countP_cons] using count) (by simpa only [Locals.get_values] using hRoot) ?_
      simpa only [lowerArgs, flatArgs, flatPointers, List.reverse_cons, List.append_assoc,
        List.head?_cons, Option.map_some, Option.getD_some, Arg.value, List.tail_cons,
        List.headD_cons, List.cons_append, List.nil_append] using h
    | output =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        held_head held (count := params.countP Param.takesArg) (by simpa [Param.takesArg, List.countP_cons] using count)
      simp only [sysLowerCode, List.cons_append, List.nil_append, wp_localGet_cons, hPlace,
        hRoot, wp_wrapI64_cons, wrap_toUInt32, Locals.get_values]
      refine wp_sys_lower params locs' values' slot _ rest Q kinds.2 (held_values held' _)
        (by simpa [Param.takesArg, List.countP_cons] using count) (by simpa only [Locals.get_values] using hRoot) ?_
      simpa only [lowerArgs, flatArgs, flatPointers, List.reverse_cons, List.append_assoc,
        List.head?_cons, Option.map_some, Option.getD_some, Arg.capacity, List.tail_cons,
        List.headD_cons, List.cons_append, List.nil_append, uint32_ofNat_toNat] using h

end Verified.Wasi
