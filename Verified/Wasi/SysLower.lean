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


/-! ## Calls with inputs

The argument code of a flat call with inputs reads each input's root and length from the two
locals of its variable.  `inputs` holds the root and the bytes of each input in turn. -/

/-- The pointers of a flat call's request with inputs: the pointer of each input in turn, the
buffer's root for its output, and the scratch address `slot`, then `slot + 8`, for its result
words. -/
def flatPointersWith : List Param → UInt32 → Nat → List UInt32 → List UInt32
  | [], _, _, _ => []
  | .input :: params, root, slot, input :: inputs =>
    input :: flatPointersWith params root slot inputs
  | .output :: params, root, slot, inputs => root :: flatPointersWith params root slot inputs
  | .result32 :: params, root, slot, inputs
  | .result64 :: params, root, slot, inputs =>
    UInt32.ofNat slot :: flatPointersWith params root (slot + 8) inputs
  | _ :: params, root, slot, inputs => flatPointersWith params root slot inputs

/-- An input's root in the local `place` and its length in the local after it. -/
def InputHeld (s : Locals) (place : Nat) (input : UInt64 × LeanExe.Bytes) : Prop :=
  s.get place = some (.i64 input.1) ∧
    s.get (place + 1) = some (.i64 (LeanExe.Bytes.size input.2)) ∧ input.2.data.size < 2 ^ 32

theorem InputHeld.values {s : Locals} {place : Nat} {input : UInt64 × LeanExe.Bytes}
    (h : InputHeld s place input) (stack : List Value) :
    InputHeld { s with values := stack } place input := by
  simpa only [InputHeld, Locals.get_values] using h

theorem inputsHeld_values {s : Locals} {places : List Nat}
    {inputs : List (UInt64 × LeanExe.Bytes)} (h : List.Forall₂ (InputHeld s) places inputs)
    (stack : List Value) : List.Forall₂ (InputHeld { s with values := stack }) places inputs :=
  h.imp fun _ _ held => held.values stack

theorem bytes_size_toUInt32 {bytes : LeanExe.Bytes} (h : bytes.data.size < 2 ^ 32) :
    (LeanExe.Bytes.size bytes).toUInt32 = UInt32.ofNat bytes.data.size := by
  have hSize := LeanExe.Bytes.size_toNat bytes (by omega)
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, hSize, Nat.mod_eq_of_lt h, UInt32.toNat_ofNat_of_lt' h]

theorem bytes_size_small {bytes : LeanExe.Bytes} (h : bytes.data.size < 2 ^ 32) :
    ¬(4294967296 : UInt64) ≤ LeanExe.Bytes.size bytes := by
  rw [UInt64.le_iff_toNat_le, LeanExe.Bytes.size_toNat bytes (by omega)]
  simp only [UInt64.reduceToNat]
  omega

/-- The first elements of two related lists. -/
theorem forall₂_head {α β : Type} {R : α → β → Prop} {xs : List α} {ys : List β} {count : Nat}
    (h : List.Forall₂ R xs ys) (length : ys.length = count + 1) :
    ∃ x y xs' ys', R x y ∧ List.Forall₂ R xs' ys' ∧ xs = x :: xs' ∧ ys = y :: ys' := by
  cases h with
  | nil => simp at length
  | cons head tail => exact ⟨_, _, _, _, head, tail, rfl, rfl⟩

/-- The input places of a request with inputs are the inputs at their pointers. -/
theorem inputPlaces_inputs {root : UInt32} :
    ∀ (params : List Param) (values : List UInt64) (inputs : List (UInt64 × LeanExe.Bytes))
      (slot : Nat),
    params.all Param.inputKind = true → inputs.length = params.count .input →
    inputPlaces params (flatArgsWith params values (inputs.map Prod.snd))
      (flatPointersWith params root slot (inputs.map fun input => input.1.toUInt32)) =
      inputs.map fun input => (input.1.toUInt32, input.2)
  | [], _, inputs, _, _, count => by
    cases inputs with
    | nil => rfl
    | cons => simp at count
  | param :: params, values, inputs, slot, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [List.map_cons, flatArgsWith, flatPointersWith, inputPlaces, List.headD_cons,
          List.head?_cons, List.tail_cons]
        rw [inputPlaces_inputs params values inputs slot kinds.2
          (by simpa [List.count_cons] using count)]
    | word32 | word64 | enum32 | flags32 | flags64 | output =>
      simp only [flatArgsWith, flatPointersWith, inputPlaces, List.tail_cons]
      exact inputPlaces_inputs params values.tail inputs slot kinds.2
        (by simpa [List.count_cons] using count)
    | result32 | result64 =>
      simp only [flatArgsWith, flatPointersWith, inputPlaces, List.tail_cons]
      exact inputPlaces_inputs params values inputs (slot + 8) kinds.2
        (by simpa [List.count_cons] using count)

/-- The test of the arguments of a call with inputs leaves the errno that rejects them, or 0. -/
theorem wp_sys_reject_inputs {α : Type} {m : Module} {st : Store α} {env : HostEnv α} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64) (inputLocs : List Nat)
      (inputs : List (UInt64 × LeanExe.Bytes)) (s : Locals) (rest : Program) (Q : Assertion α),
    params.all Param.inputKind = true →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = params.countP Param.takesWord →
    List.Forall₂ (InputHeld s) inputLocs inputs → inputs.length = params.count .input →
    wp m rest Q st { s with values := .i64 (rejectArgs params
      (flatArgsWith params values (inputs.map Prod.snd))) :: s.values } env →
    wp m (sysRejectInputsCode params locs inputLocs ++ rest) Q st s env
  | [], _, _, _, _, s, rest, Q, _, _, _, _, _, h => by
    simpa only [sysRejectInputsCode, rejectArgs, List.cons_append, List.nil_append,
      wp_constI64_cons] using h
  | param :: params, locs, values, inputLocs, inputs, s, rest, Q, kinds, held, count,
      heldInputs, inputCount, h => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | reported | record => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      obtain ⟨place, input, inputLocs', inputs', ⟨_, hLength, hSize⟩, heldInputs', rfl, rfl⟩ :=
        forall₂_head heldInputs (count := params.count .input)
          (by simpa [List.count_cons] using inputCount)
      simp only [sysRejectInputsCode, List.cons_append, wp_localGet_cons, hLength,
        wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      rw [ite_eq_right (by simp [bytes_size_small hSize])]
      rw [← List.append_nil (sysRejectInputsCode params locs inputLocs')]
      refine wp_sys_reject_inputs params locs values inputLocs' inputs' _ [] _ kinds.2
        (held_values held _) (by simpa [Param.takesWord, List.countP_cons] using count)
        (inputsHeld_values heldInputs' _) (by simpa [List.count_cons] using inputCount) ?_
      simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
        List.drop_zero]
      have hSize' : input.2.data.size < 4294967296 := hSize
      simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.length, hSize'] using h
    | flags64 mask =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      simp only [sysRejectInputsCode]
      refine wp_flags_reject hPlace (fun _ rest' Q' next => wp_sys_reject_inputs params locs'
        values' inputLocs inputs s rest' Q' kinds.2 held'
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count) heldInputs
        (by simpa [List.count_cons] using inputCount) next) ?_
      by_cases ok : value &&& ~~~(UInt64.ofNat mask) = 0 <;>
        simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value, ok] using h
    | flags32 mask =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      simp only [sysRejectInputsCode, List.cons_append, wp_localGet_cons, hPlace,
        wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
      refine wp_iff_cons rfl ?_
      by_cases large : (4294967296 : UInt64) ≤ value
      · rw [ite_eq_left (by simp [large])]
        simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
          List.cons_append, List.nil_append, List.drop_zero]
        have large' : ¬value.toNat < 4294967296 := by
          rw [UInt64.le_iff_toNat_le] at large
          simp only [UInt64.reduceToNat] at large
          omega
        simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value, large'] using h
      · rw [ite_eq_right (by simp [large])]
        have small : value.toNat < 4294967296 := by
          rw [UInt64.le_iff_toNat_le] at large
          simp only [UInt64.reduceToNat] at large
          omega
        rw [← List.append_nil
          (flagsRejectCode mask place (sysRejectInputsCode params locs' inputLocs))]
        refine wp_flags_reject (by simpa only [Locals.get_values] using hPlace)
          (fun _ rest' Q' next => wp_sys_reject_inputs params locs' values' inputLocs inputs _
            rest' Q' kinds.2 (held_values held' _)
            (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
            (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount)
            next) ?_
        simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
          List.nil_append, List.drop_zero]
        by_cases ok : value &&& ~~~(UInt64.ofNat mask) = 0 <;>
          simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value, small, ok]
            using h
    | result32 | result64 =>
      simp only [sysRejectInputsCode]
      refine wp_sys_reject_inputs params locs values inputLocs inputs s rest Q kinds.2 held
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count) heldInputs
        (by simpa [List.count_cons] using inputCount) ?_
      simpa only [rejectArgs, flatArgsWith, Param.takesArg, Bool.false_eq_true, ite_false]
        using h
    | word64 =>
      obtain ⟨place, value, locs', values', _, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      simp only [sysRejectInputsCode]
      refine wp_sys_reject_inputs params locs' values' inputLocs inputs s rest Q kinds.2 held'
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count) heldInputs
        (by simpa [List.count_cons] using inputCount) ?_
      simpa only [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, ite_true,
        List.headD_cons, List.tail_cons] using h
    | word32 | output | enum32 bound =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      have bound' : ∀ {bound : Nat}, Param.inputKind (.enum32 bound) = true →
          (UInt64.ofNat bound).toNat = bound := by
        intro bound flat
        simp only [Param.inputKind, Param.flatKind, decide_eq_true_eq] at flat
        exact UInt64.toNat_ofNat_of_lt' (by
          rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
      simp only [sysRejectInputsCode, List.cons_append, wp_localGet_cons, hPlace,
        wp_constI64_cons, wp_geUI64_cons, wp_iff_control_types]
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
             simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value,
               Arg.capacity, large'] using h
           · rw [ite_eq_right (by simp [large])]
             have small : value.toNat < 4294967296 := by
               rw [UInt64.le_iff_toNat_le] at large
               simp only [UInt64.reduceToNat] at large
               omega
             rw [← List.append_nil (sysRejectInputsCode params locs' inputLocs)]
             refine wp_sys_reject_inputs params locs' values' inputLocs inputs _ [] _ kinds.2
               (held_values held' _)
               (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
               (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount) ?_
             simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
               List.nil_append, List.drop_zero]
             simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value,
               Arg.capacity, small] using h)
        | (have bound'' := bound' kinds.1
           by_cases large : UInt64.ofNat bound ≤ value
           · rw [ite_eq_left (by simp [large])]
             simp only [wp_constI64_cons, wp_nil, List.take_succ_cons, List.take_zero,
               List.cons_append, List.nil_append, List.drop_zero]
             have large' : ¬value.toNat < bound := by
               rw [UInt64.le_iff_toNat_le, bound''] at large
               omega
             simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value,
               large'] using h
           · rw [ite_eq_right (by simp [large])]
             have small : value.toNat < bound := by
               rw [UInt64.le_iff_toNat_le, bound''] at large
               omega
             rw [← List.append_nil (sysRejectInputsCode params locs' inputLocs)]
             refine wp_sys_reject_inputs params locs' values' inputLocs inputs _ [] _ kinds.2
               (held_values held' _)
               (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
               (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount) ?_
             simp only [wp_nil, List.take_succ_cons, List.take_zero, List.cons_append,
               List.nil_append, List.drop_zero]
             simpa [rejectArgs, flatArgsWith, Param.takesArg, Param.reject, Arg.value,
               small] using h)

/-- The argument code of a call with inputs pushes the core arguments of the request whose
pointers are the inputs' roots, the buffer's root, and the scratch addresses from `slot`. -/
theorem wp_sys_lower_inputs {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {rootLocal : Nat} {root : UInt64} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64) (inputLocs : List Nat)
      (inputs : List (UInt64 × LeanExe.Bytes)) (slot : Nat) (s : Locals) (rest : Program)
      (Q : Assertion α),
    params.all Param.inputKind = true →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = params.countP Param.takesWord →
    List.Forall₂ (InputHeld s) inputLocs inputs → inputs.length = params.count .input →
    s.get rootLocal = some (.i64 root) →
    wp m rest Q st { s with values :=
      (lowerArgs params (flatArgsWith params values (inputs.map Prod.snd))
        (flatPointersWith params root.toUInt32 slot
          (inputs.map fun input => input.1.toUInt32))).reverse ++ s.values } env →
    wp m (sysLowerInputsCode params locs inputLocs rootLocal slot ++ rest) Q st s env
  | [], _, _, _, _, _, s, rest, Q, _, _, _, _, _, _, h => by
    simpa only [sysLowerInputsCode, lowerArgs, List.reverse_nil, List.nil_append] using h
  | param :: params, locs, values, inputLocs, inputs, slot, s, rest, Q, kinds, held, count,
      heldInputs, inputCount, hRoot, h => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    have hRoot' : ∀ stack : List Value,
        ({ s with values := stack } : Locals).get rootLocal = some (.i64 root) :=
      fun _ => by simpa only [Locals.get_values] using hRoot
    cases param with
    | reported | record => simp [Param.inputKind, Param.flatKind] at kinds
    | input =>
      obtain ⟨place, input, inputLocs', inputs', ⟨hInputRoot, hLength, hSize⟩, heldInputs', rfl,
        rfl⟩ := forall₂_head heldInputs (count := params.count .input)
          (by simpa [List.count_cons] using inputCount)
      simp only [sysLowerInputsCode, List.cons_append, List.nil_append, wp_localGet_cons,
        hInputRoot, wp_wrapI64_cons, wrap_toUInt32, Locals.get_values, hLength]
      refine wp_sys_lower_inputs params locs values inputLocs' inputs' slot _ rest Q kinds.2
        (held_values held _) (by simpa [Param.takesWord, List.countP_cons] using count)
        (inputsHeld_values heldInputs' _) (by simpa [List.count_cons] using inputCount)
        (hRoot' _) ?_
      simpa only [lowerArgs, flatArgsWith, flatPointersWith, List.map_cons, List.reverse_cons,
        List.append_assoc, List.head?_cons, Option.map_some, Option.getD_some, Arg.length,
        List.tail_cons, List.headD_cons, List.cons_append, List.nil_append,
        bytes_size_toUInt32 hSize] using h
    | result32 | result64 =>
      simp only [sysLowerInputsCode, List.cons_append, List.nil_append, wp_const_cons]
      refine wp_sys_lower_inputs params locs values inputLocs inputs (slot + 8) _ rest Q kinds.2
        (held_values held _)
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
        (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount)
        (hRoot' _) ?_
      simpa only [lowerArgs, flatArgsWith, flatPointersWith, List.reverse_cons,
        List.append_assoc, List.headD_cons, List.tail_cons, List.cons_append,
        List.nil_append] using h
    | word64 | flags64 =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      simp only [sysLowerInputsCode, List.cons_append, List.nil_append, wp_localGet_cons, hPlace]
      refine wp_sys_lower_inputs params locs' values' inputLocs inputs slot _ rest Q kinds.2
        (held_values held' _)
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
        (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount)
        (hRoot' _) ?_
      simpa only [lowerArgs, flatArgsWith, flatPointersWith, List.reverse_cons,
        List.append_assoc, List.head?_cons, Option.map_some, Option.getD_some, Arg.value,
        List.tail_cons, List.headD_cons, List.cons_append, List.nil_append] using h
    | word32 | enum32 | flags32 =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      simp only [sysLowerInputsCode, List.cons_append, List.nil_append, wp_localGet_cons, hPlace,
        wp_wrapI64_cons, wrap_toUInt32]
      refine wp_sys_lower_inputs params locs' values' inputLocs inputs slot _ rest Q kinds.2
        (held_values held' _)
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
        (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount)
        (hRoot' _) ?_
      simpa only [lowerArgs, flatArgsWith, flatPointersWith, List.reverse_cons,
        List.append_assoc, List.head?_cons, Option.map_some, Option.getD_some, Arg.value,
        List.tail_cons, List.headD_cons, List.cons_append, List.nil_append] using h
    | output =>
      obtain ⟨place, value, locs', values', hPlace, held', rfl, rfl⟩ :=
        forall₂_head held (count := params.countP Param.takesWord)
          (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
      simp only [sysLowerInputsCode, List.cons_append, List.nil_append, wp_localGet_cons, hPlace,
        hRoot, wp_wrapI64_cons, wrap_toUInt32, Locals.get_values]
      refine wp_sys_lower_inputs params locs' values' inputLocs inputs slot _ rest Q kinds.2
        (held_values held' _)
        (by simpa [Param.takesWord, Param.takesArg, List.countP_cons] using count)
        (inputsHeld_values heldInputs _) (by simpa [List.count_cons] using inputCount)
        (hRoot' _) ?_
      simpa only [lowerArgs, flatArgsWith, flatPointersWith, List.reverse_cons,
        List.append_assoc, List.head?_cons, Option.map_some, Option.getD_some, Arg.capacity,
        List.tail_cons, List.headD_cons, List.cons_append, List.nil_append,
        uint32_ofNat_toNat] using h

/-! ## Calls without inputs

A call whose parameters have the kinds of `flatKind` has no `input` parameter, so its forms with
inputs at no inputs are the forms without them, and the declarations without inputs follow from
those with inputs. -/

theorem inputKind_of_flat : ∀ {params : List Param}, params.all Param.flatKind = true →
    params.all Param.inputKind = true
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds ⊢
    refine ⟨?_, inputKind_of_flat kinds.2⟩
    cases param <;> simp_all [Param.inputKind, Param.flatKind]

theorem count_input_of_flat : ∀ {params : List Param}, params.all Param.flatKind = true →
    params.count .input = 0
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param <;> simp_all [Param.flatKind, List.count_cons, count_input_of_flat kinds.2]

theorem countP_takesWord_of_flat : ∀ {params : List Param}, params.all Param.flatKind = true →
    params.countP Param.takesWord = params.countP Param.takesArg
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param <;>
      simp_all [Param.flatKind, Param.takesWord, Param.takesArg, List.countP_cons,
        countP_takesWord_of_flat kinds.2]

theorem flatPointersWith_nil : ∀ (params : List Param) (root : UInt32) (slot : Nat),
    flatPointersWith params root slot [] = flatPointers params root slot
  | [], _, _ => rfl
  | param :: params, root, slot => by
    cases param <;> simp only [flatPointersWith, flatPointers, flatPointersWith_nil params]

/-- The test of the arguments leaves the errno that rejects them, or 0. -/
theorem wp_sys_reject {α : Type} {m : Module} {st : Store α} {env : HostEnv α} :
    ∀ (params : List Param) (locs : List Nat) (values : List UInt64) (s : Locals)
      (rest : Program) (Q : Assertion α),
    params.all Param.flatKind = true →
    List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values →
    values.length = params.countP Param.takesArg →
    wp m rest Q st
      { s with values := .i64 (rejectArgs params (flatArgs params values)) :: s.values } env →
    wp m (sysRejectCode params locs ++ rest) Q st s env := by
  intro params locs values s rest Q kinds held count h
  rw [← sysRejectInputsCode_nil]
  refine wp_sys_reject_inputs params locs values [] [] s rest Q (inputKind_of_flat kinds) held
    (by rw [countP_takesWord_of_flat kinds]; exact count) .nil
    (by rw [count_input_of_flat kinds]; rfl) ?_
  simpa only [List.map_nil, flatArgsWith_nil] using h

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
    wp m (sysLowerCode params locs rootLocal slot ++ rest) Q st s env := by
  intro params locs values slot s rest Q kinds held count hRoot h
  rw [← sysLowerInputsCode_nil]
  refine wp_sys_lower_inputs params locs values [] [] slot s rest Q (inputKind_of_flat kinds) held
    (by rw [countP_takesWord_of_flat kinds]; exact count) .nil
    (by rw [count_input_of_flat kinds]; rfl) hRoot ?_
  simpa only [List.map_nil, flatArgsWith_nil, flatPointersWith_nil] using h

end Verified.Wasi
