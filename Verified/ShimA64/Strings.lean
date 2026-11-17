import Verified.ShimA64.Stubs
import LeanExe.A64.Proof.WasiStrings

/-!
The shim's `sizesInvoke` and `stringsInvoke` in the terms of the runs of the stubs of
`LeanExe/A64/WasiStrings.lean`.  `vectorSize` and the bytes that the copying pass writes are the
specification's `stringsSize` and `stringsBytes` by definition, `pointerBytes` from the buffer's
address is `stringPointers`, and the bytes that `store32` stores of a count or a size are those of
`leBytes 4`.  `sizesInvoke_eq` and `stringsInvoke_eq` state the two functions for a memory of at
most 65,535 pages, the bound that `StoreRel` gives, at which the tests against `2^32` follow from
the tests against the memory's size: the trap with the store unchanged, errno 61, the count and
the size written, or the addresses and the strings written, and the trap with the event of a
count or a size of `2^32` or more.

`sizesStub_sim` and `stringsStub_sim` prove that the stubs of each vector meet `Machine.StubSim`
for the shim's function of their call on `shimMachine`.  At a stub's entry the machine's
`ScratchHolds` gives the initial SP in the scratch's first word and Linux's initial stack there,
from which `stubEntry_of` gives the vector of the launch's arguments or environment on
`wasiPlatform`, where the stub runs.  The stubs write only the guest's bytes in the area, so the
scratch and the initial stack keep their bytes, and they make no layer call, so the world's events
and the trace stay as they were.
-/

namespace Verified.ShimA64

open Wasm LeanExe LeanExe.A64 LeanExe.Wasi Verified.Wasi Verified.Shim

theorem vectorSize_eq (strs : List (List UInt8)) : vectorSize strs = stringsSize strs := rfl

theorem flatMap_zero_eq (strs : List (List UInt8)) :
    strs.flatMap (· ++ [0]) = stringsBytes strs := rfl

theorem stringsFit_iff (strs : List (List UInt8)) :
    stringsFit strs = true ↔ stringsSize strs < 2 ^ 32 := by
  have := length_le_vectorSize strs
  rw [vectorSize_eq] at this
  simp only [stringsFit, decide_eq_true_eq]
  omega

/-- Byte `k` of a word of eight bytes holding `n` is byte `k` of `n`. -/
theorem shift_byte (n k : Nat) (hk : k < 8) :
    ((UInt64.ofNat n) >>> UInt64.ofNat (8 * k)).toUInt8 = Verified.Wasi.byteOf n k := by
  apply UInt8.toNat_inj.mp
  rw [UInt64.toNat_toUInt8, UInt64.toNat_shiftRight, UInt64.toNat_ofNat', UInt64.toNat_ofNat',
    Verified.Wasi.byteOf, UInt8.toNat_ofNat', Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (show 8 * k < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 8 * k < 64 by omega)]
  have e : 2 ^ 64 = 2 ^ (8 * k) * 2 ^ (64 - 8 * k) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [e, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega : 8 ≤ 64 - 8 * k))]

/-- The bytes that four `STRB` store of the low 32 bits of a number are its four little-endian
bytes. -/
theorem word32Bytes_ofNat (n : Nat) :
    word32Bytes (UInt64.ofNat n) = (List.range 4).map (Verified.Wasi.byteOf n) := by
  show [_, _, _, _] = [Verified.Wasi.byteOf n 0, Verified.Wasi.byteOf n 1,
    Verified.Wasi.byteOf n 2, Verified.Wasi.byteOf n 3]
  have e0 := shift_byte n 0 (by decide)
  rw [Nat.mul_zero, show UInt64.ofNat 0 = 0 from rfl, UInt64.shiftRight_zero] at e0
  rw [e0, ← shift_byte n 1 (by decide), ← shift_byte n 2 (by decide),
    ← shift_byte n 3 (by decide)]

theorem leBytes_list (n : Nat) :
    (leBytes 4 n).data.data.toList = word32Bytes (UInt64.ofNat n) := by
  rw [word32Bytes_ofNat]
  rfl

/-- `stringPointers` from the buffer at `b` is `pointerBytes` from its address. -/
theorem pointerBytes_ofNat : ∀ (b : Nat) (strs : List (List UInt8)),
    pointerBytes (UInt64.ofNat b) strs = stringPointers b strs
  | _, [] => rfl
  | b, s :: rest => by
    rw [pointerBytes, stringPointers, word32Bytes_ofNat, ← UInt64.ofNat_add,
      pointerBytes_ofNat (b + (s.length + 1)) rest, Nat.add_assoc]

/-- `sizesInvoke` for a memory of at most 65,535 pages: the trap with the store unchanged when
either result's four bytes leave the memory, and otherwise errno 0 with the count and the size
written in that order, or errno 61 with the memory unchanged when the size reaches `2^32`. -/
theorem sizesInvoke_eq (strings : List (List UInt8)) (call : Call)
    (before : Store (Observed LinuxWorld)) (count size : UInt32)
    (hpages : before.mem.pages < 65536) :
    sizesInvoke strings call before [.i32 count, .i32 size] =
      if count.toNat + 4 ≤ before.mem.pages * 65536 ∧
          size.toNat + 4 ≤ before.mem.pages * 65536 then
        if stringsSize strings < 2 ^ 32 then
          .Return [.i32 0] (answered before
            ((before.mem.writeBytes count.toNat
              (word32Bytes (UInt64.ofNat strings.length))).writeBytes
              size.toNat (word32Bytes (UInt64.ofNat (stringsSize strings))))
            [] (.sys call [] (sizesReply strings)))
        else .Return [.i32 61] (answered before before.mem [] (.sys call [] (sizesReply strings)))
      else .Trap before shimTrap := by
  unfold sizesInvoke
  dsimp only
  by_cases hc : count.toNat + 4 ≤ before.mem.pages * 65536 ∧
      size.toNat + 4 ≤ before.mem.pages * 65536
  · rw [ite_eq_left ⟨hc.1, by omega, hc.2, by omega⟩, ite_eq_left hc]
    by_cases hfit : stringsSize strings < 2 ^ 32
    · have hf : stringsFit strings = true := (stringsFit_iff strings).mpr hfit
      rw [ite_eq_left hfit]
      simp only [sysAnswer, sizesReply, hf, ↓reduceIte, placeReply, sysResult, sizesOutputs,
        placeAll, leBytes_list, List.headD, List.getD_cons_succ, List.getD_cons_zero]
      rfl
    · have hf : stringsFit strings = false := by
        cases h : stringsFit strings
        · rfl
        · exact absurd ((stringsFit_iff strings).mp h) hfit
      rw [ite_eq_right hfit]
      simp only [sysAnswer, sizesReply, hf, Bool.false_eq_true, ↓reduceIte, placeReply,
        sysResult]
      rfl
  · rw [ite_eq_right (fun h => hc ⟨h.1, h.2.2.1⟩), ite_eq_right hc]

/-- `stringsInvoke` for a memory of at most 65,535 pages: the trap with the event of the call when
the size reaches `2^32`, the trap with the store unchanged when the array or the buffer leaves the
memory, and otherwise errno 0 with the addresses and then the strings written. -/
theorem stringsInvoke_eq (strings : List (List UInt8)) (call : Call)
    (before : Store (Observed LinuxWorld)) (argv buf : UInt32)
    (hpages : before.mem.pages < 65536) :
    stringsInvoke strings call before [.i32 argv, .i32 buf] =
      if stringsSize strings < 2 ^ 32 then
        if argv.toNat + 4 * strings.length ≤ before.mem.pages * 65536 ∧
            buf.toNat + stringsSize strings ≤ before.mem.pages * 65536 then
          .Return [.i32 0] (answered before
            ((before.mem.writeBytes argv.toNat (stringPointers buf.toNat strings)).writeBytes
              buf.toNat (stringsBytes strings))
            [] (.sys call [] (stringsReply strings)))
        else .Trap before shimTrap
      else
        .Trap (answered before before.mem [] (.sys call [] (stringsReply strings))) shimTrap := by
  unfold stringsInvoke
  dsimp only
  by_cases hfit : stringsSize strings < 2 ^ 32
  · have hf : stringsFit strings = true := (stringsFit_iff strings).mpr hfit
    rw [ite_eq_left hf, ite_eq_left hfit]
    by_cases hc : argv.toNat + 4 * strings.length ≤ before.mem.pages * 65536 ∧
        buf.toNat + stringsSize strings ≤ before.mem.pages * 65536
    · rw [ite_eq_left ⟨hc.1, by omega, hc.2, by omega⟩, ite_eq_left hc]
      simp only [sysAnswer, stringsReply, hf, ↓reduceIte, sysResult]
      rfl
    · rw [ite_eq_right (fun h => hc ⟨h.1, h.2.2.1⟩), ite_eq_right hc]
  · have hf : stringsFit strings = false := by
      cases h : stringsFit strings
      · rfl
      · exact absurd ((stringsFit_iff strings).mp h) hfit
    rw [ite_eq_right (by rw [hf]; decide), ite_eq_right hfit]
    simp only [sysAnswer, stringsReply, hf, Bool.false_eq_true, ↓reduceIte, sysResult]

/-! ## The stubs on the shim's machine -/

/-- The strings of the vector `v` in the launch `I`: its arguments or its environment. -/
def _root_.LeanExe.A64.StringVector.strings (I : Launch) : StringVector → List (List UInt8)
  | .args => I.args
  | .environ => I.environ

/-- The flat call of the vector `v`'s count and size. -/
def _root_.LeanExe.A64.StringVector.sizesCall : StringVector → Call
  | .args => Call.argsSizesGet
  | .environ => Call.environSizesGet

/-- The flat call of the vector `v`'s strings. -/
def _root_.LeanExe.A64.StringVector.stringsCall : StringVector → Call
  | .args => Call.argsGet
  | .environ => Call.environGet

theorem sysInvoke_sizes (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (v : StringVector) :
    sysInvoke F L I replies v.sizesCall = sizesInvoke (v.strings I) v.sizesCall := by
  cases v <;> simp (config := { decide := true }) only [sysInvoke, StringVector.sizesCall,
    StringVector.strings, ↓reduceIte]

theorem sysInvoke_strings (F : OpenFlags) (L : ShimLayout) (I : Launch) (replies : Linux.Replies)
    (v : StringVector) :
    sysInvoke F L I replies v.stringsCall = stringsInvoke (v.strings I) v.stringsCall := by
  cases v <;> simp (config := { decide := true }) only [sysInvoke, StringVector.stringsCall,
    StringVector.strings, ↓reduceIte]

/-- Two values of type `i32` from their typing. -/
theorem typed_i32x2 {args : List Value} (hlen : args.length = 2)
    (hty : Typed [.i32, .i32] args) : ∃ a0 a1 : UInt32, args = [.i32 a0, .i32 a1] := by
  match args, hlen, hty with
  | [v0, v1], _, ⟨t0, t1, _⟩ =>
    obtain ⟨a0, rfl⟩ : ∃ a, v0 = .i32 a := by
      cases v0 <;> first | exact ⟨_, rfl⟩ | exact t0.elim
    obtain ⟨a1, rfl⟩ : ∃ a, v1 = .i32 a := by
      cases v1 <;> first | exact ⟨_, rfl⟩ | exact t1.elim
    exact ⟨a0, a1, rfl⟩

theorem toUInt64_ofNat (x : UInt32) : x.toUInt64 = UInt64.ofNat x.toNat := by
  apply UInt64.toNat_inj.mp
  rw [UInt32.toNat_toUInt64,
    UInt64.toNat_ofNat_of_lt' (show x.toNat < 2 ^ 64 by have := x.toNat_lt; omega)]

/-- The trace relation after an answer of the shim without layer events. -/
theorem TraceRel.answer_nil {l₀ : List Linux.Event} {L : ShimLayout} {size : Nat}
    {h : Observed LinuxWorld} {tr : List A64.Event} (htr : TraceRel l₀ L size h tr)
    (e : Wasi.Event) : TraceRel l₀ L size ⟨h.world.answer [] e, h.events ++ [e]⟩ tr := by
  simpa [TraceRel, LinuxWorld.answer] using htr

/-- The UART of the process's platform lies outside its Normal memory when the data segment's
UART does and the initial stack lies from `2^32` up. -/
theorem wasiPlatform_uart {L : ElfLayout} {sp top : UInt64}
    (hU : (elfPlatform L).normal (elfPlatform L).uart = false) (hsp : 2 ^ 32 ≤ sp.toNat) :
    (wasiPlatform L sp top).normal (wasiPlatform L sp top).uart = false := by
  have hne : ¬ sp ≤ (elfPlatform L).uart := by
    rw [UInt64.le_iff_toNat_le]
    show ¬ sp.toNat ≤ (0 : UInt64).toNat
    simp only [UInt64.reduceToNat]
    omega
  simp only [wasiPlatform, hU, Bool.false_or, decide_eq_false_iff_not]
  exact fun h => hne h.1

variable {R : Linux.Replies} {L : ElfLayout} {G : Scratch} {I : Launch} {sp₀ top : UInt64}
  {l₀ : List Linux.Event} {calls : List LeanExe.Wasi.Call} {code : UInt64 → Option UInt32}
  {hdom : ∀ a w, code a = some w → a.toNat < 2 ^ 55}
  {hk : ∀ a w i, code a = some w → decode w = some i → i.keepsX17 = true}
  {hk18 : ∀ a w i, code a = some w → decode w = some i → i.keepsX18 = true}
  {hL : L.area.toNat + L.dataMem ≤ 2 ^ 32} {hG : G.base.toNat + scratchSize < 2 ^ 64}
  {base : UInt64} {size : Nat}

/-- What the stubs of the vector `v` read at a state of the shim's machine that holds a store of
`cap` pages, with the arguments `c` and `d` in X0 and X1, the scratch at the area's end, and the
scratch within the data segment: the scratch's first word holds the initial SP, whose initial
stack holds the launch's strings on the process's platform. -/
theorem stubEntry_of {cap : Nat} {gts : List ValueType} {st : Store (Observed LinuxWorld)}
    {q : Proc} (v : StringVector)
    (hsr : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).SR cap gts st
      q)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize cap))
    (hdm : areaSize cap + scratchSize ≤ L.dataMem) {c d : UInt32}
    (h0 : q.core.x 0 = c.toUInt64) (h1 : q.core.x 1 = d.toUInt64) :
    StubEntry (wasiPlatform L sp₀ top) (areaSize cap) (st.mem.pages * 65536) v (v.strings I)
      q.core := by
  obtain ⟨hst, -, h17, -, -, hK⟩ := hsr
  have hle := modulePlatform_le_wasi L G sp₀ top
  have hpg := hst.pages
  have hcap := hst.cap_lt
  have hA : areaSize cap = 4096 + cap * 65536 := rfl
  have hpc : st.mem.pages * 65536 ≤ cap * 65536 := Nat.mul_le_mul_right _ hpg.2
  have hP : ∀ a : UInt64, sp₀.toNat ≤ a.toNat → a.toNat < top.toNat →
      (wasiPlatform L sp₀ top).normal a = true := by
    intro a ha1 ha2
    simp only [wasiPlatform, Bool.or_eq_true, decide_eq_true_eq, UInt64.le_iff_toNat_le,
      UInt64.lt_iff_toNat_lt]
    exact .inr ⟨ha1, ha2⟩
  have hsaved : load64 q.core.mem (q.core.x 17 + UInt64.ofNat (areaSize cap)) = sp₀ := by
    rw [h17, ← hGb]
    exact hK.saved
  refine ⟨?_, fun k hk => hle.normal _ (hst.mapped k (by rw [hA]; omega)), ?_,
    fun j hj => hle.normal _ (hst.mapped (4096 + j) (by rw [hA]; omega)), ?_,
    fun _ => by rw [hsaved]; exact hK.stack.argc_word hP, ?_, ?_, ?_⟩
  · rw [hst.size, show (8 : UInt64) = UInt64.ofNat 8 from rfl, ← UInt64.ofNat_add,
      Nat.sub_add_cancel (by omega)]
  · rw [h17]
    unfold scratchSize at hdm
    omega
  · intro k hk
    rw [h17, add_ofNat_add]
    apply (elfPlatform_le_wasi L sp₀ top).normal
    have e : (L.area + UInt64.ofNat (areaSize cap + k)).toNat =
        L.area.toNat + areaSize cap + k := by
      rw [UInt64.toNat_add, UInt64.toNat_ofNat']
      unfold scratchSize at hdm
      omega
    simp only [elfPlatform, decide_eq_true_eq, UInt64.le_iff_toNat_le, e]
    unfold scratchSize at hdm
    omega
  · rw [hsaved]
    cases v
    · exact hK.stack.args_vector hP
    · exact hK.stack.environ_vector hP
  · rw [h0, UInt32.toNat_toUInt64]
    exact c.toNat_lt
  · rw [h1, UInt32.toNat_toUInt64]
    exact d.toNat_lt

/-- The stub of `args_sizes_get` or `environ_sizes_get` stands for the shim's function of its
call. -/
theorem sizesStub_sim (S : Shared) (n : Nat) (v : StringVector) {a : UInt64} {is : List Instr}
    (hg : sizesStub v a S.trapUnreachable (areaSize S.cap) = .ok is) (hcode : CodeAt code a is)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdm : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (elfPlatform L).normal (elfPlatform L).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) v.sizesCall) a := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = a at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨c, d, rfl⟩ := typed_i32x2 hlen hty
  have x0 : q.core.x 0 = c.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = d.toUInt64 := hregs 1 (by simp)
  have he := stubEntry_of v hsr hGb hdm x0 x1
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  have hpg := hst.pages
  have hcap := hst.cap_lt
  obtain ⟨t, rt, spt, iot, x17t, x18t, ht⟩ := run_sizesStub (wasiPlatform L sp₀ top) code hg
    hcode (wasiPlatform_uart hU hK.stack.above) hpc he
  rw [x0, x1, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, vectorSize_eq] at ht
  refine .inr ?_
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      v.sizesCall).invoke st [.i32 c, .i32 d] =
      sizesInvoke (v.strings I) v.sizesCall st [.i32 c, .i32 d] := by
    show sysInvoke _ _ _ _ v.sizesCall st _ = _
    rw [sysInvoke_sizes]
  rw [hinv, sizesInvoke_eq _ _ _ c d (by omega)]
  have hrch : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q
      { q with core := t } := ProcRunWith.ofReach hf rt
  by_cases hcs : c.toNat + 4 ≤ st.mem.pages * 65536 ∧ d.toNat + 4 ≤ st.mem.pages * 65536
  swap
  · rw [ite_eq_right hcs] at ht ⊢
    exact ⟨{ q with core := t }, hrch, iot, .inr (.inr (.inr ⟨rfl, ht.1⟩)), hf, htr⟩
  rw [ite_eq_left hcs] at ht ⊢
  obtain ⟨tpc, ht⟩ := ht
  have hres : ∀ w : UInt32, t.x 0 = w.toUInt64 →
      StackRel t ([Value.i32 w].take [ValueType.i32].length) := fun w hw =>
    ⟨by simp, fun k hk => by
      simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
      have hk0 : k = 0 := by omega
      subst hk0
      exact hw⟩
  by_cases hfit : stringsSize (v.strings I) < 2 ^ 32
  · rw [ite_eq_left hfit] at ht ⊢
    obtain ⟨tx0, tmem⟩ := ht
    have hlim := hst.below
    have hstk2 := hstk.limit
    have hcA : (q.core.x 17 + UInt64.ofNat (4096 + c.toNat)).toNat =
        L.area.toNat + 4096 + c.toNat := by
      rw [hst.toNat_addr (by unfold areaSize; omega), h17]; omega
    have hdA : (q.core.x 17 + UInt64.ofNat (4096 + d.toNat)).toNat =
        L.area.toNat + 4096 + d.toNat := by
      rw [hst.toNat_addr (by unfold areaSize; omega), h17]; omega
    refine ⟨{ q with core := t }, hrch, ⟨tpc, spt, x18t, iot, fun b hb => ?_, by simp,
      hres 0 (by rw [tx0]; rfl), by simp [Typed, HasType]⟩, ?_, hf, by rw [x17t, h17], by
        show _ ≤ (t.x 18).toNat
        rw [x18t]
        exact hgap, TraceRel.answer_nil htr _, ?_⟩
    · show t.mem b = q.core.mem b
      have hb' : q.core.sp.toNat ≤ b.toNat := by
        have := hb
        simp only [Nat.mul_zero, Nat.add_zero] at this
        exact this
      unfold areaSize at hgap
      rw [tmem, writeList_below (lim := q.core.x 18) (by rw [hdA, word32Bytes_length]; omega)
        (by omega), writeList_below (lim := q.core.x 18)
          (by rw [hcA, word32Bytes_length]; omega) (by omega)]
    · exact StoreRel.withHost (StoreRel.ofWriteList2 (modulePlatform L G) hst
        (by simp; omega) (by simp; omega) x17t x18t tmem) _
    · show ScratchHolds G I sp₀ top (st.host.world.events ++ []) t.mem
      rw [List.append_nil]
      refine ScratchHolds.frame hL hG hK fun b hb => ?_
      rw [tmem]
      refine (writeList_outside _ (fun i hi => ?_) b hb).trans
        (writeList_outside _ (fun i hi => ?_) b hb)
      · rw [add_ofNat_add]
        exact hst.mapped _ (by simp at hi; unfold areaSize; omega)
      · rw [add_ofNat_add]
        exact hst.mapped _ (by simp at hi; unfold areaSize; omega)
  · rw [ite_eq_right hfit] at ht ⊢
    obtain ⟨tx0, tmem⟩ := ht
    refine ⟨{ q with core := t }, hrch, ⟨tpc, spt, x18t, iot, fun b _ => by
        show t.mem b = q.core.mem b
        rw [tmem], by simp, hres 61 (by rw [tx0]; rfl), by simp [Typed, HasType]⟩,
      StoreRel.withHost (hst.regs x17t x18t tmem) _, hf, by rw [x17t, h17], by
        show _ ≤ (t.x 18).toNat
        rw [x18t]
        exact hgap, TraceRel.answer_nil htr _, ?_⟩
    show ScratchHolds G I sp₀ top (st.host.world.events ++ []) t.mem
    rw [List.append_nil, tmem]
    exact hK

/-- The stub of `args_get` or `environ_get` stands for the shim's function of its call. -/
theorem stringsStub_sim (S : Shared) (n : Nat) (v : StringVector) {a : UInt64} {is : List Instr}
    (hg : stringsStub v a S.trapUnreachable (areaSize S.cap) = .ok is) (hcode : CodeAt code a is)
    (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdm : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (elfPlatform L).normal (elfPlatform L).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      [.i32, .i32] [.i32]
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) v.stringsCall) a := by
  intro st args q hlen hty hpc hstk hsr hregs
  change Proc at q
  change q.core.pc = a at hpc
  change StackOk (modulePlatform L G) q.core at hstk
  obtain ⟨c, d, rfl⟩ := typed_i32x2 hlen hty
  have x0 : q.core.x 0 = c.toUInt64 := hregs 0 (by simp)
  have x1 : q.core.x 1 = d.toUInt64 := hregs 1 (by simp)
  have he := stubEntry_of v hsr hGb hdm x0 x1
  obtain ⟨hst, hf, h17, hgap, htr, hK⟩ := hsr
  have hpg := hst.pages
  have hcap := hst.cap_lt
  obtain ⟨t, rt, spt, iot, x17t, x18t, ht⟩ := run_stringsStub (wasiPlatform L sp₀ top) code hg
    hcode (wasiPlatform_uart hU hK.stack.above) hpc he
  rw [x0, x1, UInt32.toNat_toUInt64, UInt32.toNat_toUInt64, vectorSize_eq,
    toUInt64_ofNat d, pointerBytes_ofNat, flatMap_zero_eq] at ht
  refine .inr ?_
  have hinv : (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j))
      v.stringsCall).invoke st [.i32 c, .i32 d] =
      stringsInvoke (v.strings I) v.stringsCall st [.i32 c, .i32 d] := by
    show sysInvoke _ _ _ _ v.stringsCall st _ = _
    rw [sysInvoke_strings]
  rw [hinv, stringsInvoke_eq _ _ _ c d (by omega)]
  have hrch : (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).Rch q
      { q with core := t } := ProcRunWith.ofReach hf rt
  by_cases hfit : stringsSize (v.strings I) < 2 ^ 32
  swap
  · rw [ite_eq_right (fun h => hfit h.1)] at ht
    rw [ite_eq_right hfit]
    exact ⟨{ q with core := t }, hrch, iot, .inr (.inr (.inr ⟨rfl, ht.1⟩)), hf,
      TraceRel.answer_nil htr _⟩
  rw [ite_eq_left hfit]
  by_cases hcs : c.toNat + 4 * (v.strings I).length ≤ st.mem.pages * 65536 ∧
      d.toNat + stringsSize (v.strings I) ≤ st.mem.pages * 65536
  swap
  · rw [ite_eq_right (fun h => hcs h.2)] at ht
    rw [ite_eq_right hcs]
    exact ⟨{ q with core := t }, hrch, iot, .inr (.inr (.inr ⟨rfl, ht.1⟩)), hf, htr⟩
  rw [ite_eq_left ⟨hfit, hcs⟩] at ht
  rw [ite_eq_left hcs]
  obtain ⟨tpc, tx0, tmem⟩ := ht
  have hlim := hst.below
  have hstk2 := hstk.limit
  have hlen : (stringPointers d.toNat (v.strings I)).length = 4 * (v.strings I).length :=
    stringPointers_length _ _
  have hsz : (stringsBytes (v.strings I)).length = stringsSize (v.strings I) :=
    stringsBytes_length _
  have hcA : (q.core.x 17 + UInt64.ofNat (4096 + c.toNat)).toNat =
      L.area.toNat + 4096 + c.toNat := by
    rw [hst.toNat_addr (by unfold areaSize; omega), h17]; omega
  have hdA : (q.core.x 17 + UInt64.ofNat (4096 + d.toNat)).toNat =
      L.area.toNat + 4096 + d.toNat := by
    rw [hst.toNat_addr (by unfold areaSize; omega), h17]; omega
  refine ⟨{ q with core := t }, hrch, ⟨tpc, spt, x18t, iot, fun b hb => ?_, by simp,
    ⟨by simp, fun k hk => ?_⟩, by simp [Typed, HasType]⟩, ?_, hf, by rw [x17t, h17], by
      show _ ≤ (t.x 18).toNat
      rw [x18t]
      exact hgap, TraceRel.answer_nil htr _, ?_⟩
  · show t.mem b = q.core.mem b
    have hb' : q.core.sp.toNat ≤ b.toNat := by
      have := hb
      simp only [Nat.mul_zero, Nat.add_zero] at this
      exact this
    unfold areaSize at hgap
    rw [tmem, writeList_below (lim := q.core.x 18) (by rw [hdA, hsz]; omega)
      (by omega), writeList_below (lim := q.core.x 18) (by rw [hcA, hlen]; omega) (by omega)]
  · simp only [List.take_succ_cons, List.take_zero, List.length_cons, List.length_nil] at hk
    have hk0 : k = 0 := by omega
    subst hk0
    show t.x 0 = (0 : UInt32).toUInt64
    rw [tx0]
    rfl
  · exact StoreRel.withHost (StoreRel.ofWriteList2 (modulePlatform L G) hst
      (by rw [hlen]; omega) (by rw [hsz]; omega) x17t x18t tmem) _
  · show ScratchHolds G I sp₀ top (st.host.world.events ++ []) t.mem
    rw [List.append_nil]
    refine ScratchHolds.frame hL hG hK fun b hb => ?_
    rw [tmem]
    refine (writeList_outside _ (fun i hi => ?_) b hb).trans
      (writeList_outside _ (fun i hi => ?_) b hb)
    · rw [add_ofNat_add]
      exact hst.mapped _ (by rw [hsz] at hi; unfold areaSize; omega)
    · rw [add_ofNat_add]
      exact hst.mapped _ (by rw [hlen] at hi; unfold areaSize; omega)

/-- The data segment's UART lies outside its Normal memory when it lies outside that of the
module's platform and the scratch lies above address 0. -/
theorem elfPlatform_uart (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false)
    (hG0 : 0 < G.base.toNat) : (elfPlatform L).normal (elfPlatform L).uart = false := by
  have hne : ¬ G.base ≤ (elfPlatform L).uart := by
    rw [UInt64.le_iff_toNat_le]
    show ¬ G.base.toNat ≤ (0 : UInt64).toNat
    simp only [UInt64.reduceToNat]
    omega
  simpa [modulePlatform, hne] using hU

/-- The flat call of `shimCalls` whose name is `name`. -/
theorem shimCall_named {c : Call} (hc : c ∈ shimCalls) :
    (c.name = "args_sizes_get" → c = Call.argsSizesGet) ∧
      (c.name = "args_get" → c = Call.argsGet) ∧
      (c.name = "environ_sizes_get" → c = Call.environSizesGet) ∧
      (c.name = "environ_get" → c = Call.environGet) := by
  revert c
  decide

/-- The code of a stub of `stringStubs` at `a`, generated with the trap stub and the scratch
`areaSize S.cap` bytes above the area, stands for the shim's function of the call `c` of
`shimCalls` whose import is the stub's, when the scratch lies at the area's end and in the data
segment.  `flatStub_sim` takes its cases for these stubs from here. -/
theorem stringStub_sim {s : FlatStub} (hs : s ∈ stringStubs) {c : Call} (hc : c ∈ shimCalls)
    (hd : ABI.callImport c = s.decl) (S : Shared) (n : Nat) {a svc en : UInt64}
    {is : List Instr} (hg : s.gen a svc S.trapUnreachable en (areaSize S.cap) = .ok is)
    (hcode : CodeAt code a is) (hGb : G.base = L.area + UInt64.ofNat (areaSize S.cap))
    (hdata : areaSize S.cap + scratchSize ≤ L.dataMem)
    (hU : (modulePlatform L G).normal (modulePlatform L G).uart = false) :
    (shimMachine R L G I sp₀ top l₀ calls code hdom hk hk18 hL hG base size).StubSim S n
      s.decl.params s.decl.results
      (sysFn arm64Flags (shimLayout L.area G) I (fun j => R (l₀.length + j)) c) a := by
  have hG0 : 0 < G.base.toNat := by
    rw [hGb, UInt64.toNat_add, UInt64.toNat_ofNat']
    unfold areaSize at hdata ⊢
    omega
  have hUe := elfPlatform_uart hU hG0
  have hn : c.name = s.decl.name := congrArg ImportDecl.name hd
  obtain ⟨n1, n2, n3, n4⟩ := shimCall_named hc
  simp only [stringStubs, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · obtain rfl := n1 hn
    exact sizesStub_sim S n .args hg hcode hGb hdata hUe
  · obtain rfl := n2 hn
    exact stringsStub_sim S n .args hg hcode hGb hdata hUe
  · obtain rfl := n3 hn
    exact sizesStub_sim S n .environ hg hcode hGb hdata hUe
  · obtain rfl := n4 hn
    exact stringsStub_sim S n .environ hg hcode hGb hdata hUe

end Verified.ShimA64
