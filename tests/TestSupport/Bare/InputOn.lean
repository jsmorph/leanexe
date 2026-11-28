module

public import Verified.Reflect.Command
public import Verified.Bare
public import Verified.Call
public import TestSupport.Native.Common
public import LeanExe.Native.Proof.Input

@[expose] public section

/-!
A test of `LeanExe.Native.input_program_on` and `LeanExe.Native.EntryInRunsOn` (leanexe#30): the
program with input (`docs/native-bare-metal.md`) around an entry whose C theorem without the trap
holds only under room for the entry's generated bound.  `pushedLen` pushes a word onto a copy of
the message's words, which allocates a block of the words' length.  `pushedLen_runs` derives
`EntryInRunsOn` from two C theorems of the same C function, `ImplementsA.native` of
`compiled.pushedLen.trapFree` for the messages with room, `RoomFor`, and of
`compiled.pushedLen.implements` for the others, so that the entry's trap occurs only for a message
without that room.  `pushedLen_input` states the whole program with `input_program_on`: for every
sequence `σ` of the values that the volatile loads read, it terminates with a trace that reads
`σ`, with the result 64 for a length above `inMax`, the code of `unreachable` only for a message
without room, and otherwise the result 0 after the stores of `out`.  `roomFor` shows that every
message of at most `inMax` bytes has that room, since the cap of `nativeCap` pages holds the
block of `main` and the copy of its words, so `pushedLen_input_room` excludes the trap, in the
form `InResultRoom`.
-/

namespace TestSupport.Bare.InputOn

open Wasm LClight LeanExe.Native LeanExe.Pipeline LeanExe.ProofKit

/-- The length of the words `xs` with `v` pushed onto a copy, plus the length of `xs`. -/
def pushedLen (xs : Array UInt64) (v : UInt64) : UInt64 :=
  let ys := xs.push v
  ys.size.toUInt64 + xs.size.toUInt64

verified_compile compiled := [pushedLen]

/-- The index of `pushedLen` among the functions of `compiled.module`, after the allocator and the
release. -/
def entry : Nat := 2

/-- The heap of the store in which the translation starts. -/
abbrev heap0 : Heap := Verified.initialHeap compiled.tables

/-- The argument of the entry's call for a message of `n` bytes `b`: the words of the array that
`main` builds in the block of its allocation, and the length. -/
def argOf (n : Nat) (b : Nat → UInt8) : Array UInt64 × UInt64 :=
  let p := FixedArrayAllocate.root heap0.top (needOf n) heap0.free
  (inputWords (inputStore (heap0.allocateStore (nativeStore compiled.module nativeCap) (needOf n) 1)
    p (UInt64.ofNat (wordsOf n)) n b) p (wordsOf n), UInt64.ofNat n)

/-- The heap after the allocation of `main` leaves room for the generated bound of the entry's
call on the message of `n` bytes `b`. -/
def RoomFor (n : Nat) (b : Nat → UInt8) : Prop :=
  (heap0.allocate (needOf n)).top.toNat + compiled.pushedLen.bound (argOf n b) ≤ 65536 * nativeCap

/-- The bytes that the program stores for a message of `n` bytes `b`. -/
def out (n : Nat) (b : Nat → UInt8) : List UInt8 :=
  encodeWord (pushedLen (argOf n b).1 (argOf n b).2)

/-- The entry's C function computes `pushedLen` on the array that `main` builds, and it traps only
on a message without room for its bound: `EntryInRunsOn` from the C theorems of
`compiled.pushedLen.trapFree` and `compiled.pushedLen.implements`. -/
theorem pushedLen_runs (A : Archi) (X : ExtSem) {fd : function}
    (hfd : (funId entry, globdef.Gfun (fundef.Internal fd)) ∈
      compiled.translation.cprogram.prog_defs)
    (hsig : ∀ g, compiled.module.funcs[entry]? = some g →
      signatureOf g = some ([.i64, .i64], [.i64])) :
    EntryInRunsOn A X nativeCap compiled.module compiled.translation fd .word
      (fun n b => ¬ RoomFor n b) heap0 out := by
  have htf := ImplementsA.native (A := A) (X := X) compiled.pushedLen.trapFree
    compiled.translation_eq hfd hsig
  have himpl := ImplementsA.native (A := A) (X := X) compiled.pushedLen.implements
    compiled.translation_eq hfd hsig
  intro n hn hFits b E hE hG hcap hnres hF m1 hst hs
  set p := FixedArrayAllocate.root heap0.top (needOf n) heap0.free with hp
  set st := inputStore (heap0.allocateStore (nativeStore compiled.module nativeCap) (needOf n) 1) p
    (UInt64.ofNat (wordsOf n)) n b with hstdef
  set msg := inputWords st p (wordsOf n) with hmsg
  obtain ⟨hAt0, -, -⟩ : Verified.Ready compiled.module compiled.tables heap0
      compiled.module.initialStore := Verified.Ready.initial rfl compiled.initial
  have hheap := heapAt_nativeStore hAt0 nativeCap
  obtain ⟨hAt', hOwned, -, -⟩ := input_owned hheap hn b hFits
  have hcap' : st.memoryCap compiled.module 0 = nativeCap := by
    rw [inputStore_memoryCap, allocateStore_memoryCap, TestSupport.Native.nativeStore_memoryCap]
  have hrep : Represent.borrowed (heap0.allocate (needOf n)) st [.i64 p, .i64 (UInt64.ofNat n)]
      (msg, UInt64.ofNat n) := ⟨_, _, rfl, ⟨_, rfl, hOwned.borrowed⟩, rfl⟩
  by_cases hroom : RoomFor n b
  · obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := htf E hE hG hcap hnres hF st
      (heap0.allocate (needOf n)) [.i64 p, .i64 (UInt64.ofNat n)] (msg, UInt64.ofNat n) hAt'
      (by
        show _ + _ ≤ 65536 * st.memoryCap compiled.module 0
        rw [hcap']
        exact hroom)
      hrep Separate.nil (by rw [hcap']; decide) (argsTyped_i64 [p, UInt64.ofNat n]) m1 hst hs
    refine ⟨t, m', vres, final, hcall, hst', ?_⟩
    rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨habs, -⟩
    · exact .inl ⟨hs', outOk_word hr rfl hown⟩
    · cases habs
  · obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := himpl E hE hG hcap hnres hF st
      (heap0.allocate (needOf n)) [.i64 p, .i64 (UInt64.ofNat n)] (msg, UInt64.ofNat n) hAt'
      trivial hrep Separate.nil (by rw [hcap']; decide) (argsTyped_i64 [p, UInt64.ofNat n]) m1
      hst hs
    refine ⟨t, m', vres, final, hcall, hst', ?_⟩
    rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨-, htrap⟩
    · exact .inl ⟨hs', outOk_word hr rfl hown⟩
    · exact .inr ⟨hroom, htrap⟩

theorem top_le : heap0.top.toNat ≤ 1048576 := by decide +kernel

/-- The initial heap has room for the allocation of `main` at every length up to `inMax`. -/
theorem room (n : Nat) (hn : n ≤ inMax) :
    heap0.Room (nativeStore compiled.module nativeCap) compiled.module (needOf n) := by
  refine Heap.Within.room ?_ (by rw [TestSupport.Native.nativeStore_memoryCap]; decide)
  unfold Heap.Within
  rw [TestSupport.Native.nativeStore_memoryCap, needOf_toNat_eq hn]
  have := top_le
  unfold wordsOf inMax nativeCap at *
  omega

/-- The program with input around `pushedLen`: for every sequence `σ` of the values that the
volatile loads read, it terminates with a trace that reads `σ` and with the trace and the result
of `InResultOn`, whose trap of the entry occurs only for a message without room for its bound. -/
theorem pushedLen_input (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre) (σ : Nat → int) :
    ∃ t r, bigstep_program_terminates A X
        (inProgram pre compiled.translation (inMain nativeCap entry .word)) t r ∧
      Reads σ t ∧ InResultOn σ false (fun n b => ¬ RoomFor n b) out t r := by
  obtain ⟨fd, ps, rs, hfd, hsig, -⟩ := compiled.pushedLen.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64]) (rs0 := [.i64])
    (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] (outRet .word) cc_default := by
    rw [entry_type compiled.translation_eq hfd hsig]
    rfl
  have h0 : 0 ∈ compiled.translation.funcs :=
    translate_mem_funcs compiled.translation_eq compiled.translation_funcs (by decide)
  obtain ⟨hAt0, -, -⟩ : Verified.Ready compiled.module compiled.tables heap0
      compiled.module.initialStore := Verified.Ready.initial rfl compiled.initial
  obtain ⟨t, r, hb, hres⟩ := input_program_on compiled.translation_eq hpre
    (Verified.compileWith_runtime compiled.program compiled.tables compiled.wrappers
      compiled.literalPool).alloc h0 hfd .word hty A X (heapAt_nativeStore hAt0 nativeCap)
    (by rw [TestSupport.Native.nativeStore_memoryCap]; decide) false (fun _ => room)
    (pushedLen_runs A X hfd hsig) σ
  exact ⟨t, r, hb, hres.reads, hres⟩

/-- The allocation of `main` for a message of at most `inMax` bytes fits the initial heap. -/
theorem fits (n : Nat) (hn : n ≤ inMax) : heap0.Fits (needOf n) := by
  intro _
  have := top_le
  rw [needOf_toNat_eq hn]
  unfold wordsOf inMax at *
  omega

/-- Every message of at most `inMax` bytes leaves room for the bound of the entry's call. -/
theorem roomFor (n : Nat) (hn : n ≤ inMax) (b : Nat → UInt8) : RoomFor n b := by
  have htop := Heap.allocate_top (fits n hn)
  have := top_le
  rw [needOf_toNat_eq hn] at htop
  show _ + compiled.pushedLen.bound (_, _) ≤ _
  rw [compiled.pushedLen.bound_eq, Verified.blockCost_eq]
  simp only [inputWords, Array.size_ofFn]
  simp only [Verified.allocCost] at htop
  unfold wordsOf inMax nativeCap at *
  omega

/-- The program with input around `pushedLen` without the trap: `pushedLen_input` with the
entry's trap excluded by `roomFor`. -/
theorem pushedLen_input_room (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre) (σ : Nat → int) :
    ∃ t r, bigstep_program_terminates A X
        (inProgram pre compiled.translation (inMain nativeCap entry .word)) t r ∧
      Reads σ t ∧ InResultRoom σ out t r := by
  obtain ⟨t, r, hb, hreads, hres⟩ := pushedLen_input A X pre hpre σ
  refine ⟨t, r, hb, hreads, ?_⟩
  rcases hres with hl | ⟨hl, ⟨habs, -⟩ | ⟨hab, -⟩ | hok⟩
  · exact .inl hl
  · cases habs
  · exact absurd (roomFor _ hl _) hab
  · exact .inr ⟨hl, hok⟩

#print axioms LeanExe.Native.input_program_on
#print axioms LeanExe.Native.input_program_with
#print axioms LeanExe.Native.InResultOn.reads
#print axioms pushedLen_runs
#print axioms pushedLen_input
#print axioms pushedLen_input_room

end TestSupport.Bare.InputOn
