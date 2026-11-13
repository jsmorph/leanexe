import Verified.Wasi.SysReportedCall

/-! The parts of the code of a record call.  Its parameters are words, enums, flags, and inputs
followed by the record, so the argument test and the lowering of the parameters before the record
are those of a flat call.  The record pointer rounds the block's root up to the record's alignment,
the request places the record at that pointer after the inputs, and the loads read each field with
loads of its width. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi LeanExe.Pipeline LeanExe.Runtime LeanExe.ProofKit

/-! ## Parameters -/

theorem argKind_inputKind : ∀ {params : List Param}, params.all Param.argKind = true →
    params.all Param.inputKind = true
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds ⊢
    refine ⟨?_, argKind_inputKind kinds.2⟩
    cases param <;> simp_all [Param.argKind, Param.inputKind, Param.flatKind]

theorem argKind_count_output : ∀ {params : List Param}, params.all Param.argKind = true →
    params.count .output = 0
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param <;> simp_all [Param.argKind, argKind_count_output kinds.2]

theorem argKind_countP_result : ∀ {params : List Param}, params.all Param.argKind = true →
    params.countP Param.isResult = 0
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param <;>
      simp_all [Param.argKind, Param.isResult, argKind_countP_result kinds.2]

theorem recordOf_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ {params : List Param}, params.all Param.argKind = true →
    recordOf (params ++ [.record size align fields]) = some (size, align, fields)
  | [], _ => rfl
  | param :: params, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param <;>
      simp_all [Param.argKind, recordOf, recordOf_record size align fields kinds.2]

theorem count_input_record (size align : Nat) (fields : List (Nat × Nat)) (params : List Param) :
    (params ++ [Param.record size align fields]).count Param.input = params.count .input := by
  simp [List.count_append]

theorem countP_takesWord_record (size align : Nat) (fields : List (Nat × Nat))
    (params : List Param) :
    (params ++ [Param.record size align fields]).countP Param.takesWord =
      params.countP Param.takesWord := by
  simp [List.countP_append, Param.takesWord, Param.takesArg]

theorem flatArgsWith_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ (params : List Param) (values : List UInt64) (inputs : List LeanExe.Bytes),
    flatArgsWith (params ++ [.record size align fields]) values inputs =
      flatArgsWith params values inputs
  | [], _, inputs => by cases inputs <;> rfl
  | param :: params, values, inputs => by
    cases param <;> cases inputs <;>
      simp only [List.cons_append, flatArgsWith, flatArgsWith_record size align fields params]

theorem rejectArgs_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ (params : List Param) (args : List Arg),
    rejectArgs (params ++ [.record size align fields]) args = rejectArgs params args
  | [], args => by cases args <;> rfl
  | param :: params, args => by
    simp only [List.cons_append, rejectArgs, rejectArgs_record size align fields params]

theorem argsFit_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ (params : List Param) (args : List Arg),
    argsFit (params ++ [.record size align fields]) args = argsFit params args
  | [], _ => rfl
  | param :: params, args => by
    simp only [List.cons_append, argsFit, argsFit_record size align fields params]

theorem sysRejectInputsCode_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ (params : List Param) (words inputs : List Nat),
    sysRejectInputsCode (params ++ [.record size align fields]) words inputs =
      sysRejectInputsCode params words inputs
  | [], words, inputs => by cases words <;> cases inputs <;> rfl
  | param :: params, words, inputs => by
    cases param <;> cases words <;> cases inputs <;>
      simp only [List.cons_append, sysRejectInputsCode,
        sysRejectInputsCode_record size align fields params]

theorem sysLowerInputsCode_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ (params : List Param) (words inputs : List Nat) (root slot : Nat),
    sysLowerInputsCode (params ++ [.record size align fields]) words inputs root slot =
      sysLowerInputsCode params words inputs root slot
  | [], words, inputs, _, _ => by cases words <;> cases inputs <;> rfl
  | param :: params, words, inputs, root, slot => by
    cases param <;> cases words <;> cases inputs <;>
      simp only [List.cons_append, sysLowerInputsCode,
        sysLowerInputsCode_record size align fields params]

theorem lowerArgs_record (size align : Nat) (fields : List (Nat × Nat)) (pointer : UInt32) :
    ∀ (params : List Param) (args : List Arg) (pointers : List UInt32),
    params.all Param.argKind = true → pointers.length = params.count .input →
    lowerArgs (params ++ [.record size align fields]) args (pointers ++ [pointer]) =
      lowerArgs params args pointers ++ [.i32 pointer]
  | [], _, pointers, _, count => by
    cases pointers with
    | nil => rfl
    | cons => simp at count
  | param :: params, args, pointers, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input =>
      cases pointers with
      | nil => simp at count
      | cons first pointers =>
        simp only [List.cons_append, lowerArgs, List.headD_cons, List.tail_cons,
          lowerArgs_record size align fields pointer params args.tail pointers kinds.2
            (by simpa [List.count_cons] using count)]
    | word32 | word64 | enum32 | flags32 | flags64 =>
      simp only [List.cons_append, lowerArgs,
        lowerArgs_record size align fields pointer params args.tail pointers kinds.2
          (by simpa [List.count_cons] using count)]
    | output | result32 | result64 | reported | record => simp [Param.argKind] at kinds

theorem inputPlaces_record (size align : Nat) (fields : List (Nat × Nat)) (pointer : UInt32) :
    ∀ (params : List Param) (args : List Arg) (pointers : List UInt32),
    params.all Param.argKind = true → pointers.length = params.count .input →
    inputPlaces (params ++ [.record size align fields]) args (pointers ++ [pointer]) =
      inputPlaces params args pointers
  | [], _, pointers, _, count => by
    cases pointers with
    | nil => rfl
    | cons => simp at count
  | param :: params, args, pointers, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input =>
      cases pointers with
      | nil => simp at count
      | cons first pointers =>
        simp only [List.cons_append, inputPlaces, List.headD_cons, List.tail_cons,
          inputPlaces_record size align fields pointer params args.tail pointers kinds.2
            (by simpa [List.count_cons] using count)]
    | word32 | word64 | enum32 | flags32 | flags64 =>
      simp only [List.cons_append, inputPlaces,
        inputPlaces_record size align fields pointer params args.tail pointers kinds.2
          (by simpa [List.count_cons] using count)]
    | output | result32 | result64 | reported | record => simp [Param.argKind] at kinds

theorem outputRegions_record (size align : Nat) (fields : List (Nat × Nat)) (pointer : UInt32) :
    ∀ (params : List Param) (sizes : List Nat) (args : List Arg) (pointers : List UInt32),
    params.all Param.argKind = true → pointers.length = params.count .input →
    outputRegions (params ++ [.record size align fields]) sizes args (pointers ++ [pointer]) =
      [⟨pointer, size, align, true⟩]
  | [], _, _, pointers, _, count => by
    cases pointers with
    | nil => rfl
    | cons => simp at count
  | param :: params, sizes, args, pointers, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input =>
      cases pointers with
      | nil => simp at count
      | cons first pointers =>
        simp only [List.cons_append, outputRegions, List.tail_cons]
        exact outputRegions_record size align fields pointer params sizes args.tail pointers
          kinds.2 (by simpa [List.count_cons] using count)
    | word32 | word64 | enum32 | flags32 | flags64 =>
      simp only [List.cons_append, outputRegions]
      exact outputRegions_record size align fields pointer params sizes args.tail pointers kinds.2
        (by simpa [List.count_cons] using count)
    | output | result32 | result64 | reported | record => simp [Param.argKind] at kinds

theorem outputSizesOf_record (size align : Nat) (fields : List (Nat × Nat)) :
    ∀ (params : List Param) (sizes : List Nat) (args : List Arg),
    params.all Param.argKind = true →
    outputSizesOf (params ++ [.record size align fields]) sizes args = [size]
  | [], _, _, _ => rfl
  | param :: params, sizes, args, kinds => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | word32 | word64 | enum32 | flags32 | flags64 | input =>
      simp only [List.cons_append, outputSizesOf]
      exact outputSizesOf_record size align fields params sizes args.tail kinds.2
    | output | result32 | result64 | reported | record => simp [Param.argKind] at kinds

theorem flatPointersWith_args {root : UInt32} {slot : Nat} :
    ∀ (params : List Param) (inputs : List UInt32),
    params.all Param.argKind = true → inputs.length = params.count .input →
    flatPointersWith params root slot inputs = inputs
  | [], inputs, _, count => by
    cases inputs with
    | nil => rfl
    | cons => simp at count
  | param :: params, inputs, kinds, count => by
    simp only [List.all_cons, Bool.and_eq_true] at kinds
    cases param with
    | input =>
      cases inputs with
      | nil => simp at count
      | cons input inputs =>
        simp only [flatPointersWith]
        rw [flatPointersWith_args params inputs kinds.2 (by simpa [List.count_cons] using count)]
    | word32 | word64 | enum32 | flags32 | flags64 =>
      simp only [flatPointersWith]
      exact flatPointersWith_args params inputs kinds.2 (by simpa [List.count_cons] using count)
    | output | result32 | result64 | reported | record => simp [Param.argKind] at kinds

/-- The parameters of a call that `compiled` admits with a record. -/
theorem record_params {call : Call} {size align : Nat} {fields : List (Nat × Nat)}
    (hCompiled : call.compiled = true) (hReporter : call.reporter = none)
    (hRecord : recordOf call.params = some (size, align, fields)) :
    call.params = call.params.dropLast ++ [.record size align fields] ∧
      call.params.dropLast.all Param.argKind = true ∧ recordFits size align fields = true := by
  simp only [Call.compiled, hReporter, hRecord, Bool.and_eq_true, beq_iff_eq] at hCompiled
  obtain ⟨⟨hLast, hKinds⟩, hFits⟩ := hCompiled
  obtain ⟨prefix', hPrefix⟩ := List.getLast?_eq_some_iff.mp hLast
  refine ⟨?_, hKinds, hFits⟩
  rw [hPrefix, List.dropLast_concat]

/-! ## The record pointer -/

/-- The record pointer of a block at `root`: `root + align - 1` rounded down to a multiple of
`align`. -/
def recordAddress (root : UInt64) (align : Nat) : UInt64 :=
  (root + UInt64.ofNat (align - 1)) - (root + UInt64.ofNat (align - 1)) % UInt64.ofNat align

theorem recordAddress_spec {root : UInt64} {align : Nat} (hAlign : 0 < align)
    (hRoom : root.toNat + align ≤ 4294967296) :
    root.toNat ≤ (recordAddress root align).toNat ∧
      (recordAddress root align).toNat + 1 ≤ root.toNat + align ∧
      (recordAddress root align).toNat % align = 0 := by
  have hAlign1 : (UInt64.ofNat (align - 1)).toNat = align - 1 :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hAlignN : (UInt64.ofNat align).toNat = align :=
    UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega)
  have hSum : (root + UInt64.ofNat (align - 1)).toNat = root.toNat + (align - 1) := by
    rw [UInt64.toNat_add, hAlign1]
    exact Nat.mod_eq_of_lt (by omega)
  have hRem : ((root + UInt64.ofNat (align - 1)) % UInt64.ofNat align).toNat =
      (root.toNat + (align - 1)) % align := by
    rw [UInt64.toNat_mod, hSum, hAlignN]
  have hEq : (recordAddress root align).toNat =
      (root.toNat + (align - 1)) - (root.toNat + (align - 1)) % align := by
    rw [recordAddress, UInt64.toNat_sub_of_le _ _ (by
      rw [UInt64.le_iff_toNat_le, hRem, hSum]; exact Nat.mod_le _ _), hSum, hRem]
  have hMod := Nat.mod_lt (root.toNat + (align - 1)) hAlign
  have hDiv := Nat.div_add_mod (root.toNat + (align - 1)) align
  rw [hEq]
  generalize hA : root.toNat + (align - 1) = a at hMod hDiv
  generalize hR : a % align = r at hMod hDiv
  generalize hQ : a / align = q at hDiv
  generalize hT : align * q = t at hDiv
  have hMul : a - r = t := by omega
  refine ⟨by omega, by omega, ?_⟩
  rw [hMul, ← hT, Nat.mul_mod_right]

/-! ## The request and the call -/

/-- A record request with the inputs at their roots and the record at `pointer`. -/
theorem record_request {World : Type} {before : Store (Observed World)} {call : Call}
    {params : List Param} {size align : Nat} {fields : List (Nat × Nat)} {values : List UInt64}
    {inputs : List (UInt64 × LeanExe.Bytes)} {pointer : UInt64} {sizes : List Nat}
    (hParams : call.params = params ++ [.record size align fields])
    (hKinds : params.all Param.argKind = true)
    (hInputCount : inputs.length = params.count .input)
    (hAccepted : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0)
    (hInputAt : ∀ input ∈ inputs,
      Bytes.At before.mem input.1 input.2 ∧ input.1.toNat < 4294967296)
    (hInputApart : ∀ input ∈ inputs,
      regionsDisjoint (input.1.toNat, input.2.data.size) (pointer.toNat, size))
    (hMemory : pointer.toNat + size ≤ before.mem.pages * 65536)
    (hAddress : pointer.toNat + size < 2 ^ 32) (hAligned : pointer.toNat % align = 0) :
    SysRequest before
      (lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
        ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32]))
      call (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32]) sizes := by
  have hPointer32 : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hLength : (inputs.map fun input => input.1.toUInt32).length = params.count .input := by
    rw [List.length_map, hInputCount]
  have hArgs : flatArgsWith call.params values (inputs.map Prod.snd) =
      flatArgsWith params values (inputs.map Prod.snd) := by
    rw [hParams, flatArgsWith_record]
  have hAccepted' : rejectArgs params (flatArgsWith params values (inputs.map Prod.snd)) = 0 := by
    have h : rejectArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd)) = 0 :=
      hAccepted
    rwa [hArgs, hParams, rejectArgs_record] at h
  have hPlaces : inputPlaces call.params (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32]) =
      inputs.map fun input => (input.1.toUInt32, input.2) := by
    rw [hArgs, hParams, inputPlaces_record size align fields _ params _ _ hKinds hLength]
    have h := inputPlaces_inputs (root := 0) params values inputs 0 (argKind_inputKind hKinds)
      hInputCount
    rwa [flatPointersWith_args params _ hKinds hLength] at h
  have hRegions : outputRegions call.params sizes
      (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32]) =
      [⟨pointer.toUInt32, size, align, true⟩] := by
    rw [hParams, outputRegions_record size align fields _ params _ _ _ hKinds hLength]
  refine ⟨?_, hAccepted, rfl, ?_, ?_, ?_, ?_⟩
  · rw [hArgs, hParams, argsFit_record]
    exact flatArgsWith_fit params values _ (argKind_inputKind hKinds) (by simpa using hInputCount)
      hAccepted'
  · rw [hPlaces]
    intro place member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨at_, small⟩ := hInputAt input inputMember
    simpa only [read_narrow64 input.1 small] using at_
  · rw [hRegions]
    intro region member
    rw [List.mem_singleton] at member
    subst member
    simp only [hPointer32]
    exact ⟨hMemory, hAddress, hAligned⟩
  · rw [hRegions]
    exact List.pairwise_singleton _ _
  · rw [hRegions, hPlaces]
    intro region member place placeMember
    rw [List.mem_singleton] at member
    subst member
    obtain ⟨input, inputMember, rfl⟩ := List.mem_map.mp placeMember
    have apart := hInputApart input inputMember
    have small := (hInputAt input inputMember).2
    have hInput32 : input.1.toUInt32.toNat = input.1.toNat := by
      rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt small]
    simp only [Region.span, hPointer32, hInput32, regionsDisjoint] at apart ⊢
    omega

/-- The host call of a record request whose pointers are the inputs' roots and `pointer`: the
argument code pushes the core arguments and the record pointer, the request satisfies the call's
premise, and the contract gives the errno, the frame of the record, and on errno 0 the record at
`pointer`. -/
theorem wp_sys_record_call_with {calls : List LeanExe.Wasi.Call} {World : Type} {m : Module}
    {host : Host World} {env : HostEnv (Observed World)} {store : Store (Observed World)}
    {s : Locals} {call : LeanExe.Wasi.Call} {params : List Param} {size align : Nat}
    {fields : List (Nat × Nat)} {locs : List Nat} {values : List UInt64} {inputLocs : List Nat}
    {inputs : List (UInt64 × LeanExe.Bytes)} {rootLocal pointerLocal : Nat}
    {root pointer : UInt64} {rest : Program} {Q : Assertion (Observed World)}
    (hImports : m.imports = ABI.importsWith calls)
    (hHost : env.Satisfies m (hostSpecWith host calls))
    (hCall : calls[calls.idxOf call]? = some call)
    (hParams : call.params = params ++ [.record size align fields])
    (hKinds : params.all Param.argKind = true)
    (hAccepted : call.reject (flatArgsWith call.params values (inputs.map Prod.snd)) = 0)
    (hHeld : List.Forall₂ (fun place value => s.get place = some (.i64 value)) locs values)
    (hCount : values.length = call.wordCount)
    (hInputs : List.Forall₂ (InputHeld s) inputLocs inputs)
    (hInputCount : inputs.length = call.inputCount)
    (hRoot : s.get rootLocal = some (.i64 root))
    (hPointer : s.get pointerLocal = some (.i64 pointer))
    (hMemory : pointer.toNat + size ≤ store.mem.pages * 65536)
    (hAddress : pointer.toNat + size < 2 ^ 32) (hAligned : pointer.toNat % align = 0)
    (hInputAt : ∀ input ∈ inputs,
      Bytes.At store.mem input.1 input.2 ∧ input.1.toNat < 4294967296)
    (hInputApart : ∀ input ∈ inputs,
      regionsDisjoint (input.1.toNat, input.2.data.size) (pointer.toNat, size))
    (hNext : ∀ (final : Store (Observed World)) (errno : UInt64) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.returned errno outputs)
        final.host →
      GuestFrame store final [(pointer.toNat, size)] →
      (errno = 0 → ∃ record, outputs = [record] ∧ Bytes.At final.mem pointer record) →
      wp m rest Q final { s with values := .i32 errno.toUInt32 :: s.values } env)
    (hTrap : ∀ (final : Store (Observed World)) (message : String) (outputs : List LeanExe.Bytes),
      (observedHost host).sys store.host call
        (flatArgsWith call.params values (inputs.map Prod.snd)) (.trapped message outputs)
        final.host → Q (.Trap final message)) :
    wp m (sysLowerInputsCode call.params locs inputLocs rootLocal 0 ++
      .localGet pointerLocal :: .wrapI64 :: .call (3 + calls.idxOf call) :: rest) Q store s
      env := by
  have hPointer32 : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hInputCount' : inputs.length = params.count .input := by
    rw [hInputCount, Call.inputCount, hParams, count_input_record]
  have hCount' : values.length = params.countP Param.takesWord := by
    rw [hCount, Call.wordCount, hParams, countP_takesWord_record]
  have hLength : (inputs.map fun input => input.1.toUInt32).length = params.count .input := by
    rw [List.length_map, hInputCount']
  have hRequest := record_request (sizes := host.reported store.host.world call) hParams hKinds
    hInputCount' hAccepted hInputAt hInputApart hMemory hAddress hAligned
  have hRegions : outputRegions call.params (host.reported store.host.world call)
      (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32]) =
      [⟨pointer.toUInt32, size, align, true⟩] := by
    rw [hParams, outputRegions_record size align fields _ params _ _ _ hKinds hLength]
  have hLower : lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32]) =
      lowerArgs params (flatArgsWith params values (inputs.map Prod.snd))
        (inputs.map fun input => input.1.toUInt32) ++ [.i32 pointer.toUInt32] := by
    rw [hParams, flatArgsWith_record,
      lowerArgs_record size align fields _ params _ _ hKinds hLength]
  have hIndex : calls.idxOf call < calls.length := (List.getElem?_eq_some_iff.mp hCall).1
  rw [hParams, sysLowerInputsCode_record]
  refine wp_sys_lower_inputs params locs values inputLocs inputs 0 s _ Q (argKind_inputKind hKinds)
    hHeld hCount' hInputs hInputCount' hRoot ?_
  rw [flatPointersWith_args params _ hKinds hLength]
  simp only [wp_localGet_cons, Locals.get_values, hPointer, wp_wrapI64_cons, wrap_toUInt32]
  have hStack : Value.i32 pointer.toUInt32 ::
      ((lowerArgs params (flatArgsWith params values (inputs.map Prod.snd))
        (inputs.map fun input => input.1.toUInt32)).reverse ++ s.values) =
      (lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
        ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32])).reverse ++
        s.values := by
    rw [hLower, List.reverse_append]
    rfl
  rw [hStack]
  have hLengthArgs := lowerArgs_length call.params
    (flatArgsWith call.params values (inputs.map Prod.snd))
    ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32])
  have hTake : ((lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32])).reverse ++
        s.values).take (ABI.callImport call).params.length =
      (lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
        ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32])).reverse := by
    apply List.take_left'
    rw [List.length_reverse, hLengthArgs]
    rfl
  have hDrop : ((lowerArgs call.params (flatArgsWith call.params values (inputs.map Prod.snd))
      ((inputs.map fun input => input.1.toUInt32) ++ [pointer.toUInt32])).reverse ++
        s.values).drop (ABI.callImport call).params.length = s.values := by
    apply List.drop_left'
    rw [List.length_reverse, hLengthArgs]
    rfl
  refine wp_call_host_contract (id := 3 + calls.idxOf call) (imp := ABI.callImport call)
    (c := sysContract host call) (by rw [hImports]; exact ABI.importsWith_call hCall) hHost
    (by rw [hImports, ABI.importsWith_length]; omega) (hostSpecWith_sys host hCall) ?_ ?_ ?_
  · intro returned final contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨errno, outputs, rfl, hSys, hFrame, hShown⟩ := contract _ _ hRequest
    have hFrame' : GuestFrame store final [(pointer.toNat, size)] := by
      have h := hFrame
      simp only [hRegions, List.map_cons, List.map_nil, Region.span, hPointer32] at h
      exact h
    have hShown' :
        errno = 0 → ∃ record, outputs = [record] ∧ Bytes.At final.mem pointer record := by
      intro hZero
      have h := hShown hZero
      simp only [hRegions] at h
      cases outputs with
      | nil => simp [ShownAt] at h
      | cons record others =>
        simp only [ShownAt, ite_true] at h
        obtain ⟨at_, none⟩ := h
        subst none
        refine ⟨record, rfl, ?_⟩
        rwa [read_narrow64 pointer (by omega)] at at_
    rw [hDrop]
    simpa only [ABI.callImport, ABI.callType, List.length_cons, List.length_nil, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append] using
      hNext final errno outputs hSys hFrame' hShown'
  · intro final message contract
    rw [hTake, List.reverse_reverse] at contract
    obtain ⟨outputs, hSys, _⟩ := contract _ _ hRequest
    exact hTrap final message outputs hSys
  · intro final tag arguments contract
    rw [hTake, List.reverse_reverse] at contract
    exact (contract _ _ hRequest).elim

/-! ## The loads of the fields -/

private theorem byte_value {mem : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem pointer bytes) {index : Nat} (hIndex : index < bytes.data.size) :
    (bytes.data[index]!).toNat = (mem.bytes (pointer.toNat + index)).toNat := by
  rw [h.contents index hIndex, getElem!_pos bytes.data index hIndex]

/-- The bytes of a record from `offset` to `offset + width` lie at the record's pointer plus
`offset`. -/
theorem bytes_at_extract {mem : Mem} {root : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem root bytes) {offset width : Nat}
    (hRange : offset + width ≤ bytes.data.size) :
    Bytes.At mem (root + UInt64.ofNat offset) ⟨bytes.data.extract offset (offset + width)⟩ := by
  have hAddress := h.address
  have hMemory := h.memory
  have hRoot : (root + UInt64.ofNat offset).toNat = root.toNat + offset := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hSize : (bytes.data.extract offset (offset + width)).size = width := by
    rw [ByteArray.size_extract]; omega
  refine ⟨?_, ?_, fun i hi => ?_⟩
  · change (root + UInt64.ofNat offset).toNat +
      (bytes.data.extract offset (offset + width)).size ≤ 4294967296
    rw [hRoot, hSize]; omega
  · change (root + UInt64.ofNat offset).toNat +
      (bytes.data.extract offset (offset + width)).size ≤ mem.pages * 65536
    rw [hRoot, hSize]; omega
  · change i < (bytes.data.extract offset (offset + width)).size at hi
    have hi' : offset + i < bytes.data.size := by rw [hSize] at hi; omega
    change mem.bytes ((root + UInt64.ofNat offset).toNat + i) =
      (bytes.data.extract offset (offset + width))[i]
    rw [hRoot, show root.toNat + offset + i = root.toNat + (offset + i) by omega,
      h.contents (offset + i) hi', ByteArray.getElem_extract]

/-- A field of one byte loads as its little-endian value. -/
theorem littleEndian_read8 {mem : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem pointer bytes) (hSize : bytes.data.size = 1) {address : UInt32}
    (hAddress : address.toNat = pointer.toNat) :
    UInt64.ofNat (mem.read8 address).toUInt32.toNat = littleEndian bytes := by
  have e0 := byte_value h (index := 0) (by omega)
  have l0 := (bytes.data[0]!).toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [littleEndian, hSize, show List.range 1 = [0] from rfl, List.foldr_cons,
    List.foldr_nil]
  rw [UInt64.toNat_ofNat_of_lt' (by
    rw [show UInt64.size = 18446744073709551616 from rfl]
    have := (mem.read8 address).toUInt32.toNat_lt
    omega), UInt8.toNat_toUInt32, Mem.read8, hAddress]
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.reduceToNat]
  simp only [Nat.add_zero] at e0
  omega

/-- A field of two bytes loads as its little-endian value from two byte loads. -/
theorem littleEndian_read16 {mem : Mem} {pointer : UInt64} {bytes : LeanExe.Bytes}
    (h : Bytes.At mem pointer bytes) (hSize : bytes.data.size = 2) {low high : UInt32}
    (hLow : low.toNat = pointer.toNat) (hHigh : high.toNat = pointer.toNat + 1) :
    UInt64.ofNat (mem.read8 low).toUInt32.toNat +
      UInt64.ofNat (mem.read8 high).toUInt32.toNat * 256 = littleEndian bytes := by
  have e0 := byte_value h (index := 0) (by omega)
  have e1 := byte_value h (index := 1) (by omega)
  have l0 := (bytes.data[0]!).toNat_lt
  have l1 := (bytes.data[1]!).toNat_lt
  have m0 := (mem.read8 low).toUInt32.toNat_lt
  have m1 := (mem.read8 high).toUInt32.toNat_lt
  apply UInt64.toNat_inj.mp
  simp only [littleEndian, hSize, show List.range 2 = [0, 1] from rfl, List.foldr_cons,
    List.foldr_nil]
  have g0 : (UInt64.ofNat (mem.read8 low).toUInt32.toNat).toNat =
      (mem.bytes pointer.toNat).toNat := by
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega),
      UInt8.toNat_toUInt32, Mem.read8, hLow]
  have g1 : (UInt64.ofNat (mem.read8 high).toUInt32.toNat).toNat =
      (mem.bytes (pointer.toNat + 1)).toNat := by
    rw [UInt64.toNat_ofNat_of_lt' (by rw [show UInt64.size = 18446744073709551616 from rfl]; omega),
      UInt8.toNat_toUInt32, Mem.read8, hHigh]
  simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt8.toNat_toUInt64, UInt64.reduceToNat, g0, g1]
  simp only [Nat.add_zero] at e0
  omega

/-- The code of one field leaves the field's little-endian value. -/
theorem wp_field_load {α : Type} {m : Module} {st : Store α} {env : HostEnv α} {s : Locals}
    {place : Nat} {pointer : UInt64} {record : LeanExe.Bytes} {offset width : Nat}
    {rest : Program} {Q : Assertion α}
    (hPointer : s.get place = some (.i64 pointer)) (hAt : Bytes.At st.mem pointer record)
    (hRange : offset + width ≤ record.data.size)
    (hWidth : width = 1 ∨ width = 2 ∨ width = 4 ∨ width = 8)
    (h : wp m rest Q st
      { s with values := .i64 (littleEndian ⟨record.data.extract offset (offset + width)⟩) ::
        s.values } env) :
    wp m (fieldLoadCode place offset width ++ rest) Q st s env := by
  have hAddress := hAt.address
  have hMemory := hAt.memory
  have hField := bytes_at_extract hAt hRange
  have hFieldSize : (⟨record.data.extract offset (offset + width)⟩ : LeanExe.Bytes).data.size =
      width := by
    change (record.data.extract offset (offset + width)).size = width
    rw [ByteArray.size_extract]; omega
  have hPointer32 : pointer.toUInt32.toNat = pointer.toNat := by
    rw [UInt64.toNat_toUInt32, Nat.mod_eq_of_lt (by omega)]
  have hOffsetNat : ∀ k, k < 4294967296 → (UInt32.ofNat k).toNat = k := fun k hk =>
    UInt32.toNat_ofNat_of_lt' (by rw [show UInt32.size = 4294967296 from rfl]; omega)
  have hAdd : ∀ k, pointer.toNat + k < 4294967296 →
      (pointer.toUInt32 + UInt32.ofNat k).toNat = pointer.toNat + k := by
    intro k hk
    rw [UInt32.toNat_add, hPointer32, hOffsetNat k (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hFieldRoot : (pointer + UInt64.ofNat offset).toNat = pointer.toNat + offset := by
    rw [UInt64.toNat_add, UInt64.toNat_ofNat_of_lt' (by
      rw [show UInt64.size = 18446744073709551616 from rfl]; omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hFieldAddress : (pointer + UInt64.ofNat offset).toUInt32 =
      pointer.toUInt32 + UInt32.ofNat offset := by
    apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32, hFieldRoot, Nat.mod_eq_of_lt (by omega), hAdd offset (by omega)]
  rcases hWidth with rfl | rfl | rfl | rfl
  · simp only [fieldLoadCode, List.cons_append, List.nil_append, wp_localGet_cons, hPointer,
      wp_wrapI64_cons, wrap_toUInt32, wp_load8U_cons, hPointer32, hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    simp only [wp_extendUI32_cons]
    rwa [littleEndian_read8 hField hFieldSize (by rw [hAdd offset (by omega), hFieldRoot])]
  · simp only [fieldLoadCode, List.cons_append, List.nil_append, wp_localGet_cons, hPointer,
      wp_wrapI64_cons, wrap_toUInt32, wp_load8U_cons, hPointer32, hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    simp only [wp_extendUI32_cons, wp_localGet_cons, Locals.get_values, hPointer,
      wp_wrapI64_cons, wrap_toUInt32, wp_load8U_cons, hPointer32, hOffsetNat (offset + 1)
        (by omega)]
    rw [ite_eq_right (by omega)]
    simp only [wp_constI64_cons, wp_mulI64_cons, wp_addI64_cons]
    rwa [littleEndian_read16 hField hFieldSize (by rw [hAdd offset (by omega), hFieldRoot])
      (by rw [hAdd (offset + 1) (by omega), hFieldRoot]; omega)]
  · simp only [fieldLoadCode, List.cons_append, List.nil_append, wp_localGet_cons, hPointer,
      wp_wrapI64_cons, wrap_toUInt32, wp_load32_cons, hPointer32, hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    simp only [wp_extendUI32_cons]
    rwa [← hFieldAddress, littleEndian_read32 hField hFieldSize]
  · simp only [fieldLoadCode, List.cons_append, List.nil_append, wp_localGet_cons, hPointer,
      wp_wrapI64_cons, wrap_toUInt32, wp_load64_cons, hPointer32, hOffsetNat offset (by omega)]
    rw [ite_eq_right (by omega)]
    rwa [← hFieldAddress, littleEndian_read64 hField hFieldSize]

/-- Whether each field has a width of 1, 2, 4, or 8 bytes and lies inside a record of `size`
bytes. -/
def fieldsFit (size : Nat) (fields : List (Nat × Nat)) : Prop :=
  ∀ field ∈ fields, (field.2 = 1 ∨ field.2 = 2 ∨ field.2 = 4 ∨ field.2 = 8) ∧
    field.1 + field.2 ≤ size

theorem recordFits_fields {size align : Nat} {fields : List (Nat × Nat)}
    (h : recordFits size align fields = true) : fieldsFit size fields := by
  intro field member
  simp only [recordFits, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    beq_iff_eq] at h
  obtain ⟨width, range⟩ := h.2 field member
  refine ⟨?_, range⟩
  rcases width with ((one | two) | four) | eight
  · exact .inl one
  · exact .inr (.inl two)
  · exact .inr (.inr (.inl four))
  · exact .inr (.inr (.inr eight))

/-- The field words of a record's bytes. -/
def fieldWords (record : LeanExe.Bytes) (fields : List (Nat × Nat)) : List UInt64 :=
  fields.map fun field => littleEndian ⟨record.data.extract field.1 (field.1 + field.2)⟩

/-- The loads of the fields of a record at the pointer in local `place` into the locals from
`target`. -/
theorem wp_record_loads {α : Type} {m : Module} {st : Store α} {env : HostEnv α}
    {place : Nat} {pointer : UInt64} {record : LeanExe.Bytes} :
    ∀ (fields : List (Nat × Nat)) (target : Nat) (s : Locals) (rest : Program) (Q : Assertion α),
    s.get place = some (.i64 pointer) → Bytes.At st.mem pointer record →
    fieldsFit record.data.size fields → (place < target ∨ target + fields.length ≤ place) →
    s.params.length ≤ target → target + fields.length ≤ s.params.length + s.locals.length →
    (∀ s' : Locals, LocalsOutside s s' target fields.length →
      (∀ i, i < fields.length →
        s'.get (target + i) = some (.i64 ((fieldWords record fields).getD i 0))) →
      wp m rest Q st { s' with values := s.values } env) →
    wp m (recordLoadCode place fields target ++ rest) Q st s env
  | [], _, s, rest, Q, _, _, _, _, _, _, h => by
    simpa [recordLoadCode] using h s ⟨rfl, rfl, fun _ _ => rfl⟩ (fun i hi => by simp at hi)
  | field :: fields, target, s, rest, Q, hPointer, hAt, hFits, hPlace, hLow, hHigh, h => by
    have hHead := hFits field (List.mem_cons_self ..)
    have hTail : fieldsFit record.data.size fields := fun other member =>
      hFits other (List.mem_cons_of_mem _ member)
    have hTargetHigh : target < s.params.length + s.locals.length := by
      simp only [List.length_cons] at hHigh; omega
    simp only [recordLoadCode, List.append_assoc, List.cons_append]
    refine wp_field_load hPointer hAt hHead.2 hHead.1 ?_
    refine wp_localSet_local hLow hTargetHigh ?_
    let s1 := setLocal { s with values := s.values } target
      (.i64 (littleEndian ⟨record.data.extract field.1 (field.1 + field.2)⟩))
    have hOther : ∀ j, j ≠ target → s1.get j = s.get j := fun j hj =>
      Locals.get_setLocal_ne (s := { s with values := s.values }) hLow hj
    have hSame : s1.get target = some
        (.i64 (littleEndian ⟨record.data.extract field.1 (field.1 + field.2)⟩)) :=
      Locals.get_setLocal_same (s := { s with values := s.values }) hLow hTargetHigh
    change wp m (recordLoadCode place fields (target + 1) ++ rest) Q st s1 env
    refine wp_record_loads fields (target + 1) s1 rest Q
      ((hOther place (by simp only [List.length_cons] at hPlace; omega)).trans hPointer) hAt hTail
      (by simp only [List.length_cons] at hPlace; omega)
      (by change s.params.length ≤ target + 1; omega)
      (by simp only [s1, setLocal, List.length_set]; simp only [List.length_cons] at hHigh; omega)
      ?_
    intro s' outside held
    refine h s' ⟨outside.params, ?_, ?_⟩ ?_
    · rw [outside.length]
      simp [s1, setLocal, List.length_set]
    · intro j hj
      simp only [List.length_cons] at hj
      rw [outside.others j (by omega), hOther j (by omega)]
    · intro i hi
      cases i with
      | zero =>
        rw [Nat.add_zero, outside.others target (by omega), hSame]
        rfl
      | succ i =>
        rw [show target + (i + 1) = target + 1 + i by omega,
          held i (by simp only [List.length_cons] at hi; omega)]
        rfl

end Verified.Wasi
