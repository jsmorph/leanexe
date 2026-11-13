import Verified.Wasi.OracleHost

/-! A Talos host for the flat call imports of `hostSpecWith`, from an oracle that answers each
request of an abstract host.  The import for a call decodes the request from its core arguments,
reading each input from guest memory, asks the oracle for the reply and the next world, writes each
shown output at its region's pointer, and appends the event.  `env` places these imports after the
three stream imports of `OracleHost`, and `env_satisfies` proves that it satisfies
`hostSpecWith host calls` whenever both oracles give only replies that `host` permits. -/

namespace Verified.Wasi

open Wasm LeanExe.Wasi

/-- The span of a byte string at a pointer. -/
def placeSpan (place : UInt32 × LeanExe.Bytes) : Nat × Nat := (place.1.toNat, place.2.data.size)

/-- `mem` with each byte string written at its pointer, in order. -/
def placeAll (mem : Mem) : List (UInt32 × LeanExe.Bytes) → Mem
  | [] => mem
  | place :: places => placeAll (mem.writeBytes place.1.toNat place.2.data.data.toList) places

theorem placeAll_pages (mem : Mem) (places : List (UInt32 × LeanExe.Bytes)) :
    (placeAll mem places).pages = mem.pages := by
  induction places generalizing mem with
  | nil => rfl
  | cons place places ih => exact ih _

theorem placeAll_outside (mem : Mem) (places : List (UInt32 × LeanExe.Bytes)) (address : Nat)
    (outside : ∀ place ∈ places, ¬InRange address (placeSpan place)) :
    (placeAll mem places).bytes address = mem.bytes address := by
  induction places generalizing mem with
  | nil => rfl
  | cons place places ih =>
      simp only [placeAll]
      rw [ih _ fun other member => outside other (List.mem_cons_of_mem _ member)]
      have apart := outside place List.mem_cons_self
      simp only [InRange, placeSpan, ByteArray.size] at apart
      simp only [Mem.writeBytes, Array.length_toList]
      rw [dite_eq_right (by omega)]

theorem placeAll_at (mem : Mem) (places : List (UInt32 × LeanExe.Bytes))
    (apart : (places.map placeSpan).Pairwise LeanExe.Runtime.regionsDisjoint)
    (fits : ∀ place ∈ places, place.1.toNat + place.2.data.size ≤ 2 ^ 32 ∧
      place.1.toNat + place.2.data.size ≤ mem.pages * 65536) :
    ∀ place ∈ places, Bytes.At (placeAll mem places) place.1.toUInt64 place.2 := by
  induction places generalizing mem with
  | nil => intro _ member; cases member
  | cons first places ih =>
      rw [List.map_cons, List.pairwise_cons] at apart
      simp only [placeAll]
      have length : first.2.data.data.toList.length = first.2.data.size := by
        simp only [Array.length_toList, ByteArray.size]
      have head : Bytes.At (placeAll (mem.writeBytes first.1.toNat first.2.data.data.toList) places)
          first.1.toUInt64 first.2 := by
        have written := written_at mem first.1 first.2.data.data.toList
          (by rw [length]; exact (fits first List.mem_cons_self).1)
          (by rw [length]; exact (fits first List.mem_cons_self).2)
        rw [bytesOfList_data] at written
        refine written.frame (Nat.le_of_eq (placeAll_pages _ _).symm) ?_
        intro index bound
        apply placeAll_outside
        intro other member
        have disjoint := apart.1 (placeSpan other) (List.mem_map.mpr ⟨other, member, rfl⟩)
        simp only [InRange, placeSpan, UInt32.toNat_toUInt64,
          LeanExe.Runtime.regionsDisjoint] at disjoint ⊢
        omega
      have rest := ih (mem.writeBytes first.1.toNat first.2.data.data.toList) apart.2
        fun place member => fits place (List.mem_cons_of_mem _ member)
      intro place member
      rcases List.mem_cons.mp member with rfl | member
      · exact head
      · exact rest place member

end Verified.Wasi

namespace Verified.Wasi.OracleSys

open Wasm LeanExe.Wasi

/-- A reply and a next world for each flat call request. -/
structure Oracle (World : Type) where
  reply : World → Call → List Arg → Transfer (List LeanExe.Bytes) × World

/-- Every reply of `oracle` to a fitting, accepted request of a call in `calls` is one that `host`
permits. -/
def Oracle.Sound {World : Type} (oracle : Oracle World) (host : Host World) (calls : List Call) :
    Prop :=
  ∀ call ∈ calls, ∀ world request, argsFit call.params request = true →
    call.reject request = 0 →
    host.sys world call request (oracle.reply world call request).1
      (oracle.reply world call request).2

/-- The request and the pointers that core arguments give for the parameters `params`, with each
input read from `mem`, or `none` when the arguments do not have the parameters' core types. -/
def decodeArgs (mem : Mem) : List Param → List Value → Option (List Arg × List UInt32)
  | [], [] => some ([], [])
  | .word32 :: params, .i32 value :: values
  | .enum32 _ :: params, .i32 value :: values
  | .flags32 _ :: params, .i32 value :: values =>
    (decodeArgs mem params values).map fun decoded =>
      (.word value.toUInt64 :: decoded.1, decoded.2)
  | .word64 :: params, .i64 value :: values
  | .flags64 _ :: params, .i64 value :: values =>
    (decodeArgs mem params values).map fun decoded => (.word value :: decoded.1, decoded.2)
  | .input :: params, .i32 pointer :: .i32 length :: values =>
    (decodeArgs mem params values).map fun decoded =>
      (.bytes (bytesOfList (mem.readBytes pointer.toNat length.toNat)) :: decoded.1,
        pointer :: decoded.2)
  | .output :: params, .i32 pointer :: .i32 capacity :: values =>
    (decodeArgs mem params values).map fun decoded =>
      (.space capacity.toUInt64 :: decoded.1, pointer :: decoded.2)
  | .result32 :: params, .i32 pointer :: values
  | .result64 :: params, .i32 pointer :: values
  | .reported .. :: params, .i32 pointer :: values
  | .record .. :: params, .i32 pointer :: values =>
    (decodeArgs mem params values).map fun decoded => (decoded.1, pointer :: decoded.2)
  | _, _ => none

/-- Each shown region's pointer paired with its output, in order. -/
def shownPlaces : List Region → List LeanExe.Bytes → List (UInt32 × LeanExe.Bytes)
  | [], _ => []
  | region :: regions, outputs =>
    if region.shown then
      match outputs with
      | [] => []
      | output :: rest => (region.pointer, output) :: shownPlaces regions rest
    else shownPlaces regions outputs

variable {World : Type} (oracle : Oracle World)

/-- The store after the oracle's reply to `request`: each shown output written at its region's
pointer, the next world, and the event.  Only the regions' pointers matter here, so the regions
are computed without the reported sizes. -/
def sysAfter (call : Call) (before : Store (Observed World)) (request : List Arg)
    (pointers : List UInt32) : Store (Observed World) :=
  let transition := oracle.reply before.host.world call request
  { before with
    mem := placeAll before.mem
      (shownPlaces (outputRegions call.params [] request pointers) transition.1.committed)
    host := {
      world := transition.2
      events := before.host.events ++ [.sys call request transition.1] } }

/-- The import of `call`: decode the request, ask the oracle, and return the errno or trap with the
oracle's message.  Arguments without the parameters' core types trap. -/
def sysInvoke (call : Call) (before : Store (Observed World)) (args : List Value) :
    HostResult (Observed World) :=
  match decodeArgs before.mem call.params args with
  | some (request, pointers) =>
      let after := sysAfter oracle call before request pointers
      match (oracle.reply before.host.world call request).1 with
      | .returned errno _ => .Return [.i32 errno.toUInt32] after
      | .trapped message _ => .Trap after message
  | none => .Trap before ("host: " ++ call.name ++ " arguments are invalid")

def sysFn (call : Call) : HostFn (Observed World) where
  params := (ABI.callImport call).params
  results := (ABI.callImport call).results
  invoke := sysInvoke oracle call

theorem word_roundtrip {value : UInt64} (small : value.toNat < 2 ^ 32) :
    value.toUInt32.toUInt64 = value := by
  apply UInt64.toNat_inj.mp
  simp only [UInt32.toNat_toUInt64, UInt64.toNat_toUInt32]
  omega

/-- Decoding the core arguments of a fitting request whose inputs lie at their pointers gives the
request back, with pointers whose output regions are those of the original pointers. -/
theorem decodeArgs_lower (mem : Mem) (params : List Param) :
    ∀ (request : List Arg) (pointers : List UInt32), argsFit params request = true →
      (∀ place ∈ inputPlaces params request pointers, Bytes.At mem place.1.toUInt64 place.2) →
      ∃ decoded, decodeArgs mem params (lowerArgs params request pointers) =
          some (request, decoded) ∧
        ∀ sizes, outputRegions params sizes request decoded =
          outputRegions params sizes request pointers := by
  induction params with
  | nil =>
      intro request pointers fits _
      cases request with
      | nil => exact ⟨[], rfl, fun _ => rfl⟩
      | cons => simp [argsFit] at fits
  | cons param params ih =>
      intro request pointers fits inputs
      cases param with
      | word32 | enum32 _ | flags32 _ =>
          match request, fits, inputs with
          | .word value :: request, fits, inputs =>
              simp [argsFit, Param.takesArg, argFits] at fits
              obtain ⟨decoded, decode, same⟩ := ih request pointers fits.2 inputs
              refine ⟨decoded, ?_, same⟩
              simp [lowerArgs, decodeArgs, Arg.value, decode, word_roundtrip fits.1]
          | [], fits, _ | .bytes _ :: _, fits, _ | .space _ :: _, fits, _ =>
              simp [argsFit, Param.takesArg, argFits] at fits
      | word64 | flags64 _ =>
          match request, fits, inputs with
          | .word value :: request, fits, inputs =>
              simp [argsFit, Param.takesArg, argFits] at fits
              obtain ⟨decoded, decode, same⟩ := ih request pointers fits inputs
              refine ⟨decoded, ?_, same⟩
              simp [lowerArgs, decodeArgs, Arg.value, decode]
          | [], fits, _ | .bytes _ :: _, fits, _ | .space _ :: _, fits, _ =>
              simp [argsFit, Param.takesArg, argFits] at fits
      | input =>
          match request, fits, inputs with
          | .bytes value :: request, fits, inputs =>
              simp [argsFit, Param.takesArg, argFits] at fits
              have first : Bytes.At mem (pointers.headD 0).toUInt64 value :=
                inputs (pointers.headD 0, value) (by simp [inputPlaces])
              obtain ⟨decoded, decode, same⟩ := ih request pointers.tail fits.2
                fun place member => inputs place (by simp [inputPlaces, member])
              refine ⟨pointers.headD 0 :: decoded, ?_, fun sizes => same sizes⟩
              have length : (UInt32.ofNat value.data.size).toNat = value.data.size :=
                UInt32.toNat_ofNat_of_lt' fits.1
              have read := readBytes_value first
              rw [UInt32.toNat_toUInt64] at read
              simp [lowerArgs, decodeArgs, Arg.length, decode, length]
              simpa using read
          | [], fits, _ | .word _ :: _, fits, _ | .space _ :: _, fits, _ =>
              simp [argsFit, Param.takesArg, argFits] at fits
      | output =>
          match request, fits, inputs with
          | .space capacity :: request, fits, inputs =>
              simp [argsFit, Param.takesArg, argFits] at fits
              obtain ⟨decoded, decode, same⟩ := ih request pointers.tail fits.2 inputs
              refine ⟨pointers.headD 0 :: decoded, ?_, fun sizes => ?_⟩
              · simp [lowerArgs, decodeArgs, Arg.capacity, decode]
                apply UInt64.toNat_inj.mp
                simp only [UInt64.toNat_mod, UInt64.reduceToNat]
                omega
              · simp [outputRegions, same sizes]
          | [], fits, _ | .word _ :: _, fits, _ | .bytes _ :: _, fits, _ =>
              simp [argsFit, Param.takesArg, argFits] at fits
      | result32 | result64 | record _ _ _ =>
          obtain ⟨decoded, decode, same⟩ := ih request pointers.tail fits inputs
          refine ⟨pointers.headD 0 :: decoded, ?_, fun sizes => ?_⟩
          · simp [lowerArgs, decodeArgs, decode]
          · simp [outputRegions, same sizes]
      | reported scale align shown =>
          obtain ⟨decoded, decode, same⟩ := ih request pointers.tail fits inputs
          refine ⟨pointers.headD 0 :: decoded, ?_, fun sizes => ?_⟩
          · simp [lowerArgs, decodeArgs, decode]
          · simp [outputRegions, same sizes.tail]

theorem shownPlaces_sizes (params : List Param) :
    ∀ (sizes sizes' : List Nat) (args : List Arg) (pointers : List UInt32)
      (outputs : List LeanExe.Bytes),
      shownPlaces (outputRegions params sizes args pointers) outputs =
        shownPlaces (outputRegions params sizes' args pointers) outputs := by
  induction params with
  | nil => intros; rfl
  | cons param params ih =>
      intro sizes sizes' args pointers outputs
      cases param with
      | word32 | word64 | enum32 _ | flags32 _ | flags64 _ =>
          exact ih sizes sizes' args.tail pointers outputs
      | input => exact ih sizes sizes' args.tail pointers.tail outputs
      | output =>
          cases outputs with
          | nil => rfl
          | cons output outputs =>
              simp only [outputRegions, shownPlaces, ↓reduceIte]
              rw [ih sizes sizes' args.tail pointers.tail outputs]
      | result32 | result64 | record _ _ _ =>
          cases outputs with
          | nil => rfl
          | cons output outputs =>
              simp only [outputRegions, shownPlaces, ↓reduceIte]
              rw [ih sizes sizes' args pointers.tail outputs]
      | reported scale align shown =>
          cases shown with
          | false =>
              simp only [outputRegions, shownPlaces, Bool.false_eq_true, ↓reduceIte]
              exact ih sizes.tail sizes'.tail args pointers.tail outputs
          | true =>
              cases outputs with
              | nil => rfl
              | cons output outputs =>
                  simp only [outputRegions, shownPlaces, ↓reduceIte]
                  rw [ih sizes.tail sizes'.tail args pointers.tail outputs]

theorem outputSizes_regions (params : List Param) :
    ∀ (sizes : List Nat) (args : List Arg) (pointers : List UInt32),
      outputSizesOf params sizes args =
        ((outputRegions params sizes args pointers).filter (·.shown)).map (·.size) := by
  induction params with
  | nil => intros; rfl
  | cons param params ih =>
      intro sizes args pointers
      cases param with
      | word32 | word64 | enum32 _ | flags32 _ | flags64 _ => exact ih sizes args.tail pointers
      | input => exact ih sizes args.tail pointers.tail
      | output =>
          simp only [outputSizesOf, outputRegions]
          rw [ih sizes args.tail pointers.tail]
          rfl
      | result32 | result64 | record _ _ _ =>
          simp only [outputSizesOf, outputRegions]
          rw [ih sizes args pointers.tail]
          rfl
      | reported scale align shown =>
          simp only [outputSizesOf, outputRegions]
          rw [ih sizes.tail args pointers.tail]
          cases shown <;> rfl

theorem shownPlaces_spans (regions : List Region) :
    ∀ outputs : List LeanExe.Bytes,
      outputs.map (·.data.size) = (regions.filter (·.shown)).map (·.size) →
      (shownPlaces regions outputs).map placeSpan =
        (regions.filter (·.shown)).map Region.span := by
  induction regions with
  | nil => intro outputs _; rfl
  | cons region regions ih =>
      intro outputs sizes
      cases shown : region.shown with
      | false =>
          simp only [List.filter_cons, shown, Bool.false_eq_true, ↓reduceIte] at sizes ⊢
          simp only [shownPlaces, shown, Bool.false_eq_true, ↓reduceIte]
          exact ih outputs sizes
      | true =>
          simp only [List.filter_cons, shown, ↓reduceIte, List.map_cons] at sizes ⊢
          cases outputs with
          | nil => simp at sizes
          | cons output outputs =>
              simp only [List.map_cons, List.cons.injEq] at sizes
              simp only [shownPlaces, shown, ↓reduceIte, List.map_cons]
              rw [ih outputs sizes.2]
              simp only [placeSpan, Region.span, sizes.1]

theorem shownAt_of (mem : Mem) (regions : List Region) :
    ∀ outputs : List LeanExe.Bytes, outputs.length = (regions.filter (·.shown)).length →
      (∀ place ∈ shownPlaces regions outputs, Bytes.At mem place.1.toUInt64 place.2) →
      ShownAt mem regions outputs := by
  induction regions with
  | nil => intro outputs length _; exact List.eq_nil_of_length_eq_zero length
  | cons region regions ih =>
      intro outputs length placed
      cases shown : region.shown with
      | false =>
          simp only [List.filter_cons, shown, Bool.false_eq_true, ↓reduceIte] at length
          simp only [shownPlaces, shown, Bool.false_eq_true, ↓reduceIte] at placed
          simp only [ShownAt, shown, Bool.false_eq_true, ↓reduceIte]
          exact ih outputs length placed
      | true =>
          simp only [List.filter_cons, shown, ↓reduceIte, List.length_cons] at length
          cases outputs with
          | nil => simp at length
          | cons output outputs =>
              simp only [shownPlaces, shown, ↓reduceIte] at placed
              simp only [ShownAt, shown, ↓reduceIte]
              exact ⟨placed _ List.mem_cons_self,
                ih outputs (by simpa using length)
                  fun place member => placed place (List.mem_cons_of_mem _ member)⟩

variable {oracle} {host : Host World} {calls : List Call}

theorem sysAfter_source {call : Call} {before : Store (Observed World)} {request : List Arg}
    {pointers : List UInt32} {reply : Transfer (List LeanExe.Bytes)}
    (permitted : host.sys before.host.world call request
      (oracle.reply before.host.world call request).1
      (oracle.reply before.host.world call request).2)
    (same : (oracle.reply before.host.world call request).1 = reply) :
    (observedHost host).sys before.host call request reply
      (sysAfter oracle call before request pointers).host := by
  refine ⟨?_, ?_⟩
  · rw [← same]
    exact permitted
  · simp only [sysAfter, same]

theorem sys_contract (sound : oracle.Sound host calls) {call : Call} (member : call ∈ calls)
    (before : Store (Observed World)) (args : List Value) :
    sysContract host call before args (sysInvoke oracle call before args) := by
  intro request pointers valid
  obtain ⟨decoded, decode, same⟩ :=
    decodeArgs_lower before.mem call.params request pointers valid.fits valid.inputs
  have permitted := sound call member before.host.world request valid.fits valid.accepted
  let regions := outputRegions call.params (host.reported before.host.world call) request pointers
  let outputs := (oracle.reply before.host.world call request).1.committed
  have sizes : outputs.map (·.data.size) = (regions.filter (·.shown)).map (·.size) := by
    rw [(host.sys_bound permitted).1]
    exact outputSizes_regions call.params _ request pointers
  have places : shownPlaces (outputRegions call.params [] request decoded) outputs =
      shownPlaces regions outputs := by
    rw [shownPlaces_sizes call.params [] (host.reported before.host.world call), same]
  have spans := shownPlaces_spans regions outputs sizes
  have covered : ∀ place ∈ shownPlaces regions outputs, ∃ region ∈ regions,
      region.span = placeSpan place := by
    intro place member
    have inSpans : placeSpan place ∈ (regions.filter (·.shown)).map Region.span := by
      rw [← spans]
      exact List.mem_map.mpr ⟨place, member, rfl⟩
    obtain ⟨region, inFilter, eq⟩ := List.mem_map.mp inSpans
    exact ⟨region, List.mem_of_mem_filter inFilter, eq⟩
  have memory : (sysAfter oracle call before request decoded).mem =
      placeAll before.mem (shownPlaces regions outputs) := by
    rw [← places]
    rfl
  have frame : GuestFrame before (sysAfter oracle call before request decoded)
      (regions.map Region.span) := by
    refine ⟨rfl, ?_, ?_⟩
    · rw [memory, placeAll_pages]
    · intro address outside
      rw [memory]
      apply placeAll_outside
      intro place member
      obtain ⟨region, regionMember, eq⟩ := covered place member
      rw [← eq]
      exact outside _ (List.mem_map.mpr ⟨region, regionMember, rfl⟩)
  have shown : ShownAt (sysAfter oracle call before request decoded).mem regions outputs := by
    rw [memory]
    apply shownAt_of
    · simpa using congrArg List.length sizes
    · apply placeAll_at
      · rw [spans]
        exact valid.apart.sublist (List.filter_sublist.map _)
      · intro place member
        obtain ⟨region, regionMember, eq⟩ := covered place member
        have bounds := valid.bounds region regionMember
        simp only [placeSpan, Region.span, Prod.mk.injEq] at eq
        rw [← eq.1, ← eq.2]
        exact ⟨bounds.2.1, bounds.1⟩
  rw [valid.arguments]
  simp only [sysInvoke, decode]
  cases reply : (oracle.reply before.host.world call request).1 with
  | returned errno committed =>
      refine ⟨errno, committed, rfl, sysAfter_source permitted reply, frame, fun _ => ?_⟩
      have fixed : outputs = committed := by simp only [outputs, reply, Transfer.committed]
      rw [← fixed]
      exact shown
  | trapped message committed =>
      exact ⟨committed, sysAfter_source permitted reply, frame⟩

/-- The three stream imports from `streams`, then one import for each call in `calls` from
`oracle`. -/
def env (streams : OracleHost.Oracle World) (oracle : Oracle World) (calls : List Call) :
    HostEnv (Observed World) :=
  { funcs := [OracleHost.readFn streams, OracleHost.writeFn streams, OracleHost.exitFn streams] ++
      calls.map (sysFn oracle) }

theorem env_satisfies {streams : OracleHost.Oracle World} (streamsSound : streams.Sound host)
    (sound : oracle.Sound host calls) (target : Wasm.Module)
    (imports : target.imports = ABI.importsWith calls) :
    (env streams oracle calls).Satisfies target (hostSpecWith host calls) := by
  intro index bound
  rw [imports, ABI.importsWith_length] at bound
  match index, bound with
  | 0, _ =>
      exact ⟨OracleHost.readFn streams, readContract host, rfl, hostSpecWith_read host calls,
        OracleHost.read_contract streamsSound⟩
  | 1, _ =>
      exact ⟨OracleHost.writeFn streams, writeContract host, rfl, hostSpecWith_write host calls,
        OracleHost.write_contract streamsSound⟩
  | 2, _ =>
      exact ⟨OracleHost.exitFn streams, exitContract host, rfl, hostSpecWith_exit host calls,
        OracleHost.exit_contract streamsSound⟩
  | position + 3, bound =>
      have inCalls : position < calls.length := by omega
      refine ⟨sysFn oracle calls[position], sysContract host calls[position], ?_, ?_,
        sys_contract sound (List.getElem_mem inCalls)⟩
      · simp [env, inCalls]
      · rw [Nat.add_comm]
        exact hostSpecWith_sys host (List.getElem?_eq_getElem inCalls)

end Verified.Wasi.OracleSys
