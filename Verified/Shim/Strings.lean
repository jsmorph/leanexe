import Verified.Shim.SysEnv

/-!
The shim's `args_sizes_get`, `args_get`, `environ_sizes_get`, and `environ_get`, which make no
call.  `sizesInvoke strings` stores the count and the size of `strings` at the two result
pointers, or answers errno 61 when either reaches `2^32`; `stringsInvoke strings` writes the
pointers to the strings at `argv` and the strings with their terminating zeros at `buf`, as
Wasmtime 44 lays them out, or traps when the count or the size reaches `2^32`.  The strings are
the arguments or the environment of `Launch`.  `sizes_contract` and `strings_contract` prove, for
the host `linuxHost F L I replies`, the specification of a call with the parameters of the sizes
and of the strings, given the call's image.
-/

namespace Verified.Shim

open Wasm LeanExe LeanExe.Wasi Verified.Wasi

variable (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)

/-- `args_sizes_get` or `environ_sizes_get` for `strings`, with the pointers of the count and the
size. -/
def sizesInvoke (strings : List (List UInt8)) (call : Call) (before : Store (Observed LinuxWorld))
    (args : List Value) : HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 count, .i32 size] =>
    if count.toNat + 4 ≤ before.mem.pages * 65536 ∧ count.toNat + 4 < 2 ^ 32 ∧
        size.toNat + 4 ≤ before.mem.pages * 65536 ∧ size.toNat + 4 < 2 ^ 32 then
      sysAnswer before call []
        (placeReply before.mem
          (fun outputs => [(count, outputs.headD Bytes.empty), (size, outputs.getD 1 Bytes.empty)])
          (sizesReply strings))
        [] (sizesReply strings)
    else .Trap before shimTrap
  | _ => .Trap before shimTrap

/-- The four little-endian bytes of the address of each of `strings`, laid out one after another
from `base`, each followed by its terminating zero. -/
def stringPointers (base : Nat) : List (List UInt8) → List UInt8
  | [] => []
  | s :: rest => (List.range 4).map (byteOf base) ++ stringPointers (base + s.length + 1) rest

/-- `args_get` or `environ_get` for `strings`, with the pointers of the address array and of the
buffer. -/
def stringsInvoke (strings : List (List UInt8)) (call : Call) (before : Store (Observed LinuxWorld))
    (args : List Value) : HostResult (Observed LinuxWorld) :=
  match args with
  | [.i32 argv, .i32 buf] =>
    if stringsFit strings then
      if argv.toNat + 4 * strings.length ≤ before.mem.pages * 65536 ∧
          argv.toNat + 4 * strings.length < 2 ^ 32 ∧
          buf.toNat + stringsSize strings ≤ before.mem.pages * 65536 ∧
          buf.toNat + stringsSize strings < 2 ^ 32 then
        sysAnswer before call []
          ((before.mem.writeBytes argv.toNat (stringPointers buf.toNat strings)).writeBytes
            buf.toNat (stringsBytes strings))
          [] (stringsReply strings)
      else .Trap before shimTrap
    else sysAnswer before call [] before.mem [] (stringsReply strings)
  | _ => .Trap before shimTrap

theorem stringPointers_length (base : Nat) (strings : List (List UInt8)) :
    (stringPointers base strings).length = 4 * strings.length := by
  induction strings generalizing base with
  | nil => rfl
  | cons s rest ih =>
    simp only [stringPointers, List.length_append, List.length_map, List.length_range, ih,
      List.length_cons]
    omega

theorem sizes_contract {call : Call} {strings : List (List UInt8)}
    (params : call.params = [.result32, .result32])
    (image : ∀ events, SysImage F L I events call [] (sizesReply strings) [])
    (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) call before args (sizesInvoke strings call before args) := by
  apply sys_contract_of
  intro request pointers valid
  have empty : request = [] := by
    have fits := valid.fits
    rw [params] at fits
    simpa [argsFit, Param.takesArg] using fits
  subst empty
  have regions : outputRegions call.params (shimReported I before.host.world.reports call) []
      pointers = [⟨pointers.headD 0, 4, 4, true⟩, ⟨pointers.tail.headD 0, 4, 4, true⟩] := by
    rw [params]
    rfl
  have first := valid.bounds ⟨pointers.headD 0, 4, 4, true⟩ (by rw [regions]; simp)
  have second := valid.bounds ⟨pointers.tail.headD 0, 4, 4, true⟩ (by rw [regions]; simp)
  have apart := valid.apart
  rw [regions] at apart
  have arguments : args = [.i32 (pointers.headD 0), .i32 (pointers.tail.headD 0)] := by
    rw [valid.arguments, params]
    rfl
  subst arguments
  have check : (pointers.headD 0).toNat + 4 ≤ before.mem.pages * 65536 ∧
      (pointers.headD 0).toNat + 4 < 2 ^ 32 ∧
      (pointers.tail.headD 0).toNat + 4 ≤ before.mem.pages * 65536 ∧
      (pointers.tail.headD 0).toNat + 4 < 2 ^ 32 := ⟨first.1, first.2.1, second.1, second.2.1⟩
  dsimp only
  rw [regions]
  have agree : ∀ outputs : List Bytes, outputs.map (·.data.size) =
      (([⟨pointers.headD 0, 4, 4, true⟩, ⟨pointers.tail.headD 0, 4, 4, true⟩] : List Region).filter
        (·.shown)).map (·.size) →
      [(pointers.headD 0, outputs.headD Bytes.empty),
        (pointers.tail.headD 0, outputs.getD 1 Bytes.empty)] =
        OracleSys.shownPlaces [⟨pointers.headD 0, 4, 4, true⟩, ⟨pointers.tail.headD 0, 4, 4, true⟩]
          outputs := by
    intro outputs sizes
    rcases outputs with _ | ⟨o0, _ | ⟨o1, _ | ⟨o2, rest⟩⟩⟩
    · simp at sizes
    · simp at sizes
    · rfl
    · simp at sizes
  have inside : ∀ region ∈ ([⟨pointers.headD 0, 4, 4, true⟩, ⟨pointers.tail.headD 0, 4, 4, true⟩] :
      List Region), region.pointer.toNat + region.size ≤ before.mem.pages * 65536 ∧
        region.pointer.toNat + region.size < 2 ^ 32 := by
    intro region member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact ⟨first.1, first.2.1⟩
    · exact ⟨second.1, second.2.1⟩
  have answer := placed (regions := [⟨pointers.headD 0, 4, 4, true⟩,
    ⟨pointers.tail.headD 0, 4, 4, true⟩]) (sizesReply_shape strings) agree inside apart
  refine ⟨_, [], sizesReply strings, ?_, shimStep_none ⟨valid.accepted, image _⟩, answer.1,
    answer.2⟩
  simp only [sizesInvoke, check, and_self, ↓reduceIte]

/-- The pointers and the strings written apart: the strings lie at `buf`. -/
theorem strings_at {mem : Mem} {argv buf : UInt32} {strings : List (List UInt8)}
    (fits : buf.toNat + stringsSize strings < 2 ^ 32)
    (memory : buf.toNat + stringsSize strings ≤ mem.pages * 65536) :
    Bytes.At ((mem.writeBytes argv.toNat (stringPointers buf.toNat strings)).writeBytes buf.toNat
      (stringsBytes strings)) buf.toUInt64 (bytesOfList (stringsBytes strings)) :=
  written_at _ buf _ (by rw [stringsBytes_length]; omega)
    (by simp only [Mem.writeBytes, stringsBytes_length]; exact memory)

theorem strings_contract {call : Call} {strings : List (List UInt8)}
    (params : call.params = [.reported 4 4 false, .reported 1 1 true])
    (reported : ∀ reports, shimReported I reports call = call.sizesOf (sizesOutputs strings))
    (image : ∀ events, SysImage F L I events call [] (stringsReply strings) [])
    (before : Store (Observed LinuxWorld)) (args : List Value) :
    sysContract (linuxHost F L I replies) call before args
      (stringsInvoke strings call before args) := by
  apply sys_contract_of
  intro request pointers valid
  have empty : request = [] := by
    have fits := valid.fits
    rw [params] at fits
    simpa [argsFit, Param.takesArg] using fits
  subst empty
  have arguments : args = [.i32 (pointers.headD 0), .i32 (pointers.tail.headD 0)] := by
    rw [valid.arguments, params]
    rfl
  subst arguments
  dsimp only
  by_cases fits : stringsFit strings = true
  · have small := fits
    simp only [stringsFit, decide_eq_true_eq] at small
    have count : (littleEndian (leBytes 4 strings.length)).toNat = strings.length := by
      rw [littleEndian_leBytes (by omega) (show strings.length < 2 ^ (8 * 4) by omega),
        UInt64.toNat_ofNat_of_lt' (show strings.length < 2 ^ 64 by omega)]
    have size : (littleEndian (leBytes 4 (stringsSize strings))).toNat = stringsSize strings := by
      rw [littleEndian_leBytes (by omega) (show stringsSize strings < 2 ^ (8 * 4) by omega),
        UInt64.toNat_ofNat_of_lt' (show stringsSize strings < 2 ^ 64 by omega)]
    have regions : outputRegions call.params (shimReported I before.host.world.reports call) []
        pointers = [⟨pointers.headD 0, 4 * strings.length, 4, false⟩,
          ⟨pointers.tail.headD 0, stringsSize strings, 1, true⟩] := by
      rw [reported, params]
      simp [Call.sizesOf, params, reportedSizesOf, sizesOutputs, outputRegions, count, size]
    have first := valid.bounds ⟨pointers.headD 0, 4 * strings.length, 4, false⟩
      (by rw [regions]; simp)
    have second := valid.bounds ⟨pointers.tail.headD 0, stringsSize strings, 1, true⟩
      (by rw [regions]; simp)
    have check : (pointers.headD 0).toNat + 4 * strings.length ≤ before.mem.pages * 65536 ∧
        (pointers.headD 0).toNat + 4 * strings.length < 2 ^ 32 ∧
        (pointers.tail.headD 0).toNat + stringsSize strings ≤ before.mem.pages * 65536 ∧
        (pointers.tail.headD 0).toNat + stringsSize strings < 2 ^ 32 :=
      ⟨first.1, first.2.1, second.1, second.2.1⟩
    rw [regions]
    refine ⟨(before.mem.writeBytes (pointers.headD 0).toNat
        (stringPointers (pointers.tail.headD 0).toNat strings)).writeBytes
        (pointers.tail.headD 0).toNat (stringsBytes strings), [], stringsReply strings, ?_,
      shimStep_none ⟨valid.accepted, image _⟩, ?_, ?_⟩
    · simp only [stringsInvoke, fits, ↓reduceIte, check, and_self]
    · refine (MemFrame.writeBytes _ _ _ ?_).trans (MemFrame.writeBytes _ _ _ ?_)
      · refine ⟨_, List.mem_cons_self, Nat.le_refl _, ?_⟩
        simp [stringPointers_length, Region.span]
      · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, ?_⟩
        simp [stringsBytes_length, Region.span]
    · intro outputs same
      simp only [stringsReply, fits, ↓reduceIte] at same
      obtain ⟨_, rfl⟩ := Transfer.returned.inj same
      simp only [ShownAt, Bool.false_eq_true, ↓reduceIte]
      exact ⟨strings_at second.2.1 second.1, trivial⟩
  · refine ⟨before.mem, [], stringsReply strings, ?_, shimStep_none ⟨valid.accepted, image _⟩,
      MemFrame.refl _ _, fun outputs same => ?_⟩
    · simp only [stringsInvoke, fits, Bool.false_eq_true, ↓reduceIte]
    · simp only [stringsReply, fits, Bool.false_eq_true, ↓reduceIte] at same
      cases same

end Verified.Shim
