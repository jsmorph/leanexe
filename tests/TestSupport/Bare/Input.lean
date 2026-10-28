import Library.Hashing.Sha256.Bytes
import TestSupport.Native.Common
import LeanExe.Native.Proof.Input
import Verified.Bare

/-!
The theorem of the program with input of milestone B7 (`docs/native-bare-metal.md`): `main` with
input around the export `sha256` of `Library.Hashing.Sha256.compiled`, function 11, whose four
results `main` writes from the result globals.  For every sequence `σ` of the values that the
volatile loads of `lx_in` read, `sha256_input` states that the program terminates with a trace
that reads `σ` and with the trace and result that `InResult` describes: for a length `n` of at
most `inMax`, the result 0 after the loads of the length and of the `n` bytes `b` and the stores
of the 32 bytes of `SHS.SHA256.Impl.sha256` of the message, or the code of `unreachable` after
the loads of the length when `alloc` traps.  `sha256_correct` of the transcription of FIPS 180-4
equates `Impl.sha256` with the standard's digest.
-/

namespace TestSupport.Bare

open Wasm LClight LeanExe.Native LeanExe.Pipeline LeanExe.ProofKit
open Library.Hashing.Sha256 Library.Hashing.Words Library.Bytes

/-- The message of the `n` bytes `b 0` to `b (n - 1)`. -/
def message (n : Nat) (b : Nat → UInt8) : ByteArray := ⟨(Array.range n).map b⟩

/-- The output of the program for the message: the 32 bytes of its SHA-256 digest. -/
def shaOut (n : Nat) (b : Nat → UInt8) : List UInt8 :=
  (SHS.SHA256.Impl.sha256 (message n b)).toList

theorem encodeWords_bytes (d : Words4) :
    encodeWords [d.w0, d.w1, d.w2, d.w3] = (d.bytes 32).toList := by
  simp [encodeWords, encodeWord, Words4.bytes, Library.Bytes.byteAt, List.range_succ,
    Vector.toList_ofFn, List.ofFn_succ]

theorem bytes_message {ws : Array UInt64} {n : Nat} {b : Nat → UInt8}
    (h : ∀ i < n, Library.Bytes.byteAt ws i = b i) : bytes ws n = message n b := by
  unfold bytes message
  congr 1
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    exact h i (by simpa using h1)

/-- The entry `sha256` of the translation, on the array that `main` builds, computes the digest of
the message. -/
theorem sha256_runs (A : Archi) (X : ExtSem) {fd : function}
    (hnat : Verified.NativeTablesA A X nativeCap compiled.module compiled.translation
      [.i64, .i64] [.i64, .i64, .i64, .i64] fd false
      (fun x : Array UInt64 × UInt64 => sha256 x.1 x.2) [(4096, roundConstants)]
      (fun _ _ _ => True) (fun _ _ _ _ _ => True))
    (h4 : 4 ≤ compiled.translation.nres) :
    EntryInRuns A X nativeCap compiled.module compiled.translation fd (.words 4) false
      (Verified.initialHeap compiled.tables) shaOut := by
  intro n hn hFits b E hE hG hcap hnres hF m1 hst hs
  set heap0 := Verified.initialHeap compiled.tables with hheap0
  set p := FixedArrayAllocate.root heap0.top (needOf n) heap0.free with hp
  set st := inputStore (heap0.allocateStore (nativeStore compiled.module nativeCap) (needOf n) 1) p
    (UInt64.ofNat (wordsOf n)) n b with hstdef
  set msg := inputWords st p (wordsOf n) with hmsg
  obtain ⟨hAt0, hK0, -⟩ := ready_initial
  have hheap := heapAt_nativeStore hAt0 nativeCap
  obtain ⟨hAt', hOwned, hWithin, hbytes⟩ := input_owned hheap hn b hFits
  have hK := Heap.Borrowed.allocate_within (Verified.borrowed_nativeStore hK0 nativeCap) hheap
    hFits hWithin
  have hcap' : st.memoryCap compiled.module 0 ≤ 65535 := by
    rw [inputStore_memoryCap, allocateStore_memoryCap, TestSupport.Native.nativeStore_memoryCap]
    decide
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap hnres hF st
    (heap0.allocate (needOf n)) [.i64 p, .i64 (UInt64.ofNat n)] (msg, UInt64.ofNat n) hAt' trivial
    (fun t ht => by
      simp only [List.mem_singleton] at ht
      subst ht
      exact ⟨hK, Apart.nil⟩)
    ⟨_, _, rfl, ⟨_, rfl, hOwned.borrowed⟩, rfl⟩ Separate.nil hcap'
    (argsTyped_i64 [p, UInt64.ofNat n]) m1 hst hs
  refine ⟨t, m', vres, final, hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨habs, -⟩
  · obtain ⟨ws, hws, -, rfl, -, hin⟩ := hr
    let d := sha256 msg (UInt64.ofNat n)
    have hv : vs.reverse = [Value.i64 d.w0, .i64 d.w1, .i64 d.w2, .i64 d.w3] := hown
    have hws' : ws = [.i64 d.w3, .i64 d.w2, .i64 d.w1, .i64 d.w0] := by
      have : vs = ws := by simpa using hws
      subst this
      simpa using congrArg List.reverse hv
    subst hws'
    let w : Nat → UInt64 := fun i => [d.w0, d.w1, d.w2, d.w3].getD i 0
    refine .inl ⟨hs', w, by omega, fun i hi => ?_, ?_⟩
    · obtain ⟨v, hvi, -, hl⟩ := hin i (by simpa using hi)
      interval_cases i <;> simp at hvi <;> subst hvi <;> exact hl
    · have hn61 : (UInt64.ofNat n).toNat < 2 ^ 61 := by
        rw [toNat_ofNat64 (by unfold inMax at hn; omega)]
        unfold inMax at hn
        omega
      have hmsgb : bytes msg (UInt64.ofNat n).toNat = message n b := by
        rw [toNat_ofNat64 (by unfold inMax at hn; omega)]
        exact bytes_message fun i hi => hbytes i hi
      show shaOut n b = encodeWords [d.w0, d.w1, d.w2, d.w3]
      rw [encodeWords_bytes, sha256_bytes _ _ hn61, hmsgb]
      rfl
  · cases habs

/-- The program with input around the export `sha256`: for every sequence `σ` of the values that
the volatile loads read, it terminates with a trace that reads `σ`, with the trace and the result
of `InResult` for the output `shaOut`. -/
theorem sha256_input (A : Archi) (X : ExtSem) (pre : List (ident × globdef (fundef function) type))
    (hpre : PrefixOk pre) (σ : Nat → int) :
    ∃ t r, bigstep_program_terminates A X
        (inProgram pre compiled.translation (inMain nativeCap 11 (.words 4))) t r ∧
      Reads σ t ∧ InResult σ false shaOut t r := by
  obtain ⟨fd, ps, rs, hfd, hsig, hnat⟩ := compiled.sha256.native A X
  obtain ⟨rfl, rfl⟩ := TestSupport.Native.sig_of hsig (ps0 := [.i64, .i64])
    (rs0 := [.i64, .i64, .i64, .i64]) (by decide +kernel)
  have hty : type_of_function fd = .Tfunction [tulong, tulong] (outRet (.words 4)) cc_default := by
    rw [entry_type compiled.translation_eq hfd hsig]
    rfl
  have h0 : 0 ∈ compiled.translation.funcs :=
    translate_mem_funcs compiled.translation_eq compiled.translation_funcs (by decide)
  have h4 : 4 ≤ compiled.translation.nres := by
    rw [translate_nres compiled.translation_eq,
      translate_funcs_eq compiled.translation_eq compiled.translation_funcs]
    decide +kernel
  obtain ⟨hAt0, -, -⟩ := ready_initial
  obtain ⟨t, r, hb, hres⟩ := input_program compiled.translation_eq hpre
    (Verified.compileWith_runtime compiled.program compiled.tables compiled.wrappers
      compiled.literalPool).alloc h0 hfd (.words 4) hty A X (heapAt_nativeStore hAt0 nativeCap)
    (by rw [TestSupport.Native.nativeStore_memoryCap]; decide) (sha256_runs A X hnat h4) σ
  exact ⟨t, r, hb, hres.reads, hres⟩

end TestSupport.Bare
