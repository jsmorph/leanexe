module

public import Demos.BignumCalc.MessageCost
public import LeanExe.Native.Proof.Input
public import LeanExe.Dialect.Lemmas
public import Verified.Call
public import Verified.BoundFacts
import all Init.Data.Repr
import all Init.Data.Int.Repr

@[expose] public section

/-!
# The calculator on bare metal

The program is the C translation of `messageCompiled.module` with `lx_mem` of `nativeCap` pages,
followed by `lx_in`, `lx_out`, and the `main` of `LeanExe.Native.inMain` around function 44,
`calcWords`.  `main` reads from `lx_in` a length `n` in eight bytes, the lowest first, and then `n`
bytes of message, copies them into an array that it allocates with `alloc`, calls `calcWords` on
the array and `n`, and writes the bytes of the returned array to `lx_out`: its length word and then
its words, each the lowest byte first.  It returns 0, or 64 without reading the message when `n`
exceeds `inMax`, `2 ^ 24 - 8`.

`calc_program` states that for every sequence `σ` of the values that the volatile loads of `lx_in`
read, the program terminates: with result 0 after the loads of the length and of the message and
the stores of `calcOut n b`, the bytes of `calcSpec`'s line packed in words, when `n ≤ inMax`, and
with result 64 after the loads of the length otherwise.  `calc_line` writes the output as bytes: the
number of words, the line, and zeros to the end of its last word.  `calc_unary`, `calc_binary`, and
`calc_zero_divisor` join the program's theorem with the main claims: for a message that names an
operation and gives Lean's texts of integers, the line is `0`, a space, and Lean's text of the
exact result, or `3` for a division by zero.

The message reaches the program through the volatile loads of `lx_in`, whose values the theorems
take as any sequence `σ`; on QEMU's `virt` machine the generic loader places the length and the
message's bytes at `lx_in`, `0x70000000`.  The theorems concern the program in leanexe's Lean copy
of CompCert's Clight, whose semantics gives each frame unbounded memory, so no theorem bounds the
stack: leanexe's stack-bound tool bounds the stack of `main` from the compiled assembly when the
program is built.  The step to CompCert's assembly program is leanexe's Rocq theorem
`clight2_bigstep_asm_reads`, with the comparison of the whole program with `clightgen`'s reading,
outside Lean.
-/

namespace Demos.BignumCalc

open Library.Numerics.Bignum

open LClight LeanExe.Native LeanExe.Pipeline LeanExe.ProofKit LeanExe.Dialect
open Library.Numerics.Decimal.Shared.StrconvGrammar (ascii words)

/-! ## The output -/

/-- The bytes that the program writes for a message of `n` bytes `b`: the length word and the
words of the message's line, packed eight bytes to a word. -/
def calcOut (n : Nat) (b : Nat → UInt8) : List UInt8 :=
  encodeArray (pack (words (calcSpec ((List.range n).map b))))

/-- Byte `8 j + i` of the bytes of a list of words is byte `i` of word `j`. -/
theorem flatMap_encodeWord_getElem (xs : List UInt64) {j i : Nat} (hj : j < xs.length)
    (hi : i < 8) :
    (xs.flatMap encodeWord)[8 * j + i]? = some ((xs[j] >>> UInt64.ofNat (8 * i)).toUInt8) := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons x rest ih =>
    have hlen : (encodeWord x).length = 8 := by simp [encodeWord]
    rw [List.flatMap_cons]
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · rw [List.getElem?_append_left (by rw [hlen]; omega)]
      simp [encodeWord, hi]
    · rw [List.getElem?_append_right (by rw [hlen]; omega), hlen,
        show 8 * j + i - 8 = 8 * (j - 1) + i by omega, ih (by simp at hj; omega)]
      simp only [List.getElem_cons, show j ≠ 0 by omega, dite_false]

theorem length_flatMap_encodeWord (xs : List UInt64) :
    (xs.flatMap encodeWord).length = 8 * xs.length := by
  induction xs with
  | nil => simp
  | cons x rest ih => simp [List.flatMap_cons, ih, encodeWord]; omega

/-- The bytes of `pack (words l)` are `l` followed by zeros to the end of its last word. -/
theorem pack_bytes (l : List UInt8) (hl : l.length < 2 ^ 32) :
    (pack (words l)).toList.flatMap encodeWord =
      l ++ List.replicate ((l.length + 7) / 8 * 8 - l.length) 0 := by
  have hsz : (pack (words l)).size = (l.length + 7) / 8 := by
    rw [pack, build_size, words_size, UInt64.toNat_div, UInt64.toNat_add,
      natToUInt64_toNat (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  apply List.ext_getElem?
  intro q
  have hq : q = 8 * (q / 8) + q % 8 := by omega
  by_cases hin : q / 8 < (pack (words l)).size
  · rw [hq, flatMap_encodeWord_getElem _ (by simpa using hin) (by omega)]
    simp only [Array.getElem_toList]
    rw [pack_byte l hl hin (by omega)]
    rw [← hq]
    by_cases hql : q < l.length
    · rw [List.getElem?_append_left hql, List.getElem?_eq_getElem hql]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hql]
    · rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
      rw [hsz] at hin
      rw [ite_eq_left_iff.mpr (fun h => absurd (by omega) h)]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show l.length ≤ q by omega)]
  · rw [List.getElem?_eq_none (by rw [length_flatMap_encodeWord]; simp; omega),
      List.getElem?_eq_none (by simp; rw [hsz] at hin; omega)]

/-- The bytes that the program writes: the number of words of the line, the line, and zeros to the
end of its last word. -/
theorem calcOut_eq (n : Nat) (b : Nat → UInt8) (hn : n ≤ inMax) :
    calcOut n b =
      encodeWord (UInt64.ofNat (((calcSpec ((List.range n).map b)).length + 7) / 8)) ++
        calcSpec ((List.range n).map b) ++
          List.replicate (((calcSpec ((List.range n).map b)).length + 7) / 8 * 8 -
            (calcSpec ((List.range n).map b)).length) 0 := by
  have hl : (calcSpec ((List.range n).map b)).length < 2 ^ 32 := by
    have := calcSpec_length_le ((List.range n).map b)
    simp only [List.length_map, List.length_range] at this
    unfold inMax at hn
    omega
  have hsz : (pack (words (calcSpec ((List.range n).map b)))).size =
      ((calcSpec ((List.range n).map b)).length + 7) / 8 := by
    rw [pack, build_size, words_size, UInt64.toNat_div, UInt64.toNat_add,
      natToUInt64_toNat (by omega)]
    simp only [UInt64.reduceToNat]
    omega
  rw [calcOut, encodeArray, hsz, pack_bytes _ hl, List.append_assoc]

/-! ## The entry's call without a trap -/

set_option maxRecDepth 100000 in
/-- Function 44, from a store in which `top` can rise by `2 ^ 25` bytes, returns `calcWords ws n`
without a trap and raises `top` by at most that much. -/
theorem calcWords_trapFree :
    ImplementsA false messageCompiled.module 44
      (fun x : Array UInt64 × UInt64 => calcWords x.1 x.2)
      (fun _ heap store => heap.Within store messageCompiled.module (2 ^ 25))
      (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 2 ^ 25) :=
  messageCompiled.calcWords.trapFree.mono
    (fun x _ _ h => h.mono (calcWords_bound_le x.1 x.2))
    fun x _ _ _ _ _ h => h.trans (Nat.add_le_add_left (calcWords_bound_le x.1 x.2) _)

/-! ## The run of the entry on the message -/

theorem allocSize_toNat_le {bytes : UInt64} (h : bytes.toNat ≤ 4294967296) :
    (allocSize bytes).toNat ≤ bytes.toNat + 8 := by
  have hRound : ((bytes + 7) / 8 * 8).toNat = (bytes.toNat + 7) / 8 * 8 := by
    simp only [UInt64.toNat_mul, UInt64.toNat_div, UInt64.toNat_add, UInt64.reduceToNat]
    omega
  unfold allocSize
  split
  · simp only [UInt64.reduceToNat]
    omega
  · rw [hRound]
    omega

/-- The payload that `main` allocates for a message of at most `inMax` bytes. -/
theorem needOf_le {n : Nat} (hn : n ≤ inMax) : (needOf n).toNat ≤ 2 ^ 24 + 16 := by
  have hw := wordsOf_le hn
  have hsz : UInt64.size = 2 ^ 64 := rfl
  have hb : (UInt64.ofNat (8 + 8 * wordsOf n)).toNat = 8 + 8 * wordsOf n :=
    UInt64.toNat_ofNat_of_lt' (by rw [hsz]; omega)
  have := allocSize_toNat_le (bytes := UInt64.ofNat (8 + 8 * wordsOf n)) (by omega)
  unfold needOf
  unfold wordsOf inMax at *
  omega

theorem calc_initialHeap_top :
    (Verified.initialHeap messageCompiled.tables).top.toNat = 4096 := by
  decide +kernel

theorem calc_nativeStore_memoryCap :
    (nativeStore messageCompiled.module nativeCap).memoryCap messageCompiled.module 0 = 4096 :=
  rfl

/-- The initial heap has room for the message of every length up to `inMax`. -/
theorem calc_room (n : Nat) (hn : n ≤ inMax) :
    (Verified.initialHeap messageCompiled.tables).Room
      (nativeStore messageCompiled.module nativeCap) messageCompiled.module (needOf n) := by
  refine Heap.Within.room ?_ (by rw [calc_nativeStore_memoryCap]; decide)
  unfold Heap.Within
  rw [calc_initialHeap_top, calc_nativeStore_memoryCap]
  have := needOf_le hn
  omega

/-- The entry `calcWords`, on the array that `main` builds from a message of `n` bytes `b`,
returns without a trap the words of `calcOut n b`. -/
theorem calcWords_runs (A : Archi) (X : ExtSem) {fd : function}
    (hnat : NativeA A X nativeCap messageCompiled.module messageCompiled.translation
      [.i64, .i64] [.i64] fd false (fun x : Array UInt64 × UInt64 => calcWords x.1 x.2)
      (fun _ heap store => heap.Within store messageCompiled.module (2 ^ 25))
      (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat + 2 ^ 25)) :
    EntryInRuns A X nativeCap messageCompiled.module messageCompiled.translation fd .array false
      (Verified.initialHeap messageCompiled.tables) calcOut := by
  intro n hn hFits b E hE hG hcap hnres hF m1 hst hs
  have hsz : UInt64.size = 2 ^ 64 := rfl
  set heap0 := Verified.initialHeap messageCompiled.tables with hheap0
  set p := FixedArrayAllocate.root heap0.top (needOf n) heap0.free with hp
  set st := inputStore (heap0.allocateStore (nativeStore messageCompiled.module nativeCap)
    (needOf n) 1) p (UInt64.ofNat (wordsOf n)) n b with hstdef
  set msg := inputWords st p (wordsOf n) with hmsg
  obtain ⟨hAt0, -, -⟩ : Verified.Ready messageCompiled.module messageCompiled.tables heap0
      messageCompiled.module.initialStore := Verified.Ready.initial rfl messageCompiled.initial
  have hheap := heapAt_nativeStore hAt0 nativeCap
  obtain ⟨hAt', hOwned, -, hbytes⟩ := input_owned hheap hn b hFits
  have hcapSt : st.memoryCap messageCompiled.module 0 = 4096 := by
    rw [inputStore_memoryCap, allocateStore_memoryCap, calc_nativeStore_memoryCap]
  have hPre : (heap0.allocate (needOf n)).Within st messageCompiled.module (2 ^ 25) := by
    have htop := Heap.allocate_top hFits
    have hneed := needOf_le hn
    unfold Heap.Within
    rw [hcapSt]
    rw [Verified.allocCost, calc_initialHeap_top] at htop
    unfold inMax at hn
    omega
  obtain ⟨t, m', vres, final, hcall, hst', hres⟩ := hnat E hE hG hcap hnres hF st
    (heap0.allocate (needOf n)) [.i64 p, .i64 (UInt64.ofNat n)] (msg, UInt64.ofNat n) hAt' hPre
    ⟨_, _, rfl, ⟨_, rfl, hOwned.borrowed⟩, rfl⟩ Separate.nil (by rw [hcapSt]; decide)
    (argsTyped_i64 [p, UInt64.ofNat n]) m1 hst hs
  refine ⟨t, m', vres, final, hcall, hst', ?_⟩
  rcases hres with ⟨hs', vs, heap', hr, -, hown, -⟩ | ⟨habs, -⟩
  · have heq : calcWords msg (UInt64.ofNat n) = pack (words (calcSpec ((List.range n).map b))) := by
      rw [calcWords_eq msg n (by unfold inMax at hn; omega)]
      congr 3
      exact List.map_congr_left fun i hi => hbytes i (List.mem_range.mp hi)
    have hout : OutOk A E .array final m' vres
        (encodeArray (calcWords msg (UInt64.ofNat n))) := outOk_array hr rfl hown
    rw [heq] at hout
    exact .inl ⟨hs', hout⟩
  · cases habs

/-! ## The program -/

/-- For every sequence `σ` of the values that the volatile loads of `lx_in` read, the program
terminates.  For a length `n` of at most `inMax`, it terminates with result 0 after the loads of
the length and of the `n` bytes `b` of the message and the stores to `lx_out` of the bytes of
`calcOut n b`, and for a longer length with result 64 after the loads of the length.  The trace
reads `σ`, the premise `reads` of the Rocq theorem that carries the termination to CompCert's
assembly program.  The theorem holds under every `Archi`, every semantics of external functions,
and every list `pre` of CompCert's declarations that `PrefixOk` accepts. -/
theorem calc_program (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) :
    ∃ t r, bigstep_program_terminates A X
        (inProgram pre messageCompiled.translation (inMain nativeCap 44 .array)) t r ∧
      Reads σ t ∧ InResultRoom σ calcOut t r := by
  obtain ⟨fd, ps, rs, hfd, hsig, -⟩ := messageCompiled.calcWords.native A X
  obtain ⟨rfl, rfl⟩ := sig_eq hsig (ps0 := [.i64, .i64]) (rs0 := [.i64]) (by decide +kernel)
  have hnat := ImplementsA.native (A := A) (X := X) calcWords_trapFree
    messageCompiled.translation_eq hfd hsig
  have hty : type_of_function fd = .Tfunction [tulong, tulong] (outRet .array) cc_default := by
    rw [entry_type messageCompiled.translation_eq hfd hsig]
    rfl
  have h0 : 0 ∈ messageCompiled.translation.funcs :=
    translate_mem_funcs messageCompiled.translation_eq messageCompiled.translation_funcs
      (by decide)
  obtain ⟨hAt0, -, -⟩ : Verified.Ready messageCompiled.module messageCompiled.tables
      (Verified.initialHeap messageCompiled.tables) messageCompiled.module.initialStore :=
    Verified.Ready.initial rfl messageCompiled.initial
  obtain ⟨t, r, hb, hres⟩ := LeanExe.Native.input_program_room messageCompiled.translation_eq hpre
    (Verified.compileWith_runtime messageCompiled.program messageCompiled.tables
      messageCompiled.wrappers messageCompiled.literalPool).alloc h0 hfd .array hty A X
    (heapAt_nativeStore hAt0 nativeCap) (by rw [calc_nativeStore_memoryCap]; decide)
    calc_room (calcWords_runs A X hnat) σ
  exact ⟨t, r, hb, hres.inResult.reads, hres⟩

/-! ## The program and the main claims -/

/-- The message that the program reads: `n` bytes from the loads of `lx_in`. -/
def inMsg (σ : Nat → int) : List UInt8 := (List.range (inLen σ).toNat).map (inMsgByte σ)

theorem inMsg_length (σ : Nat → int) : (inMsg σ).length = (inLen σ).toNat := by
  simp [inMsg]

theorem inLen_le_of_msgMax {σ : Nat → int} (h : (inMsg σ).length ≤ msgMax) :
    (inLen σ).toNat ≤ inMax := by
  rw [← inMsg_length]; unfold msgMax at h; unfold inMax; omega

/-- For every message of at most `inMax` bytes, the program terminates with result 0 after the
loads of the length and of the message and the stores of the number of words of the message's
line, the line, and zeros to the end of its last word. -/
theorem calc_line (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) (hlen : (inLen σ).toNat ≤ inMax) :
    ∃ t : trace, bigstep_program_terminates A X
        (inProgram pre messageCompiled.translation (inMain nativeCap 44 .array)) t 0 ∧
      Reads σ t ∧ t = inTrace σ 0 (8 + (inLen σ).toNat) ++
        outTrace (encodeWord (UInt64.ofNat (((calcSpec (inMsg σ)).length + 7) / 8)) ++
          calcSpec (inMsg σ) ++
          List.replicate (((calcSpec (inMsg σ)).length + 7) / 8 * 8 - (calcSpec (inMsg σ)).length)
            0) := by
  obtain ⟨t, r, hb, hreads, hok'⟩ := calc_program A X pre hpre σ
  rcases hok' with ⟨hlong, -, -⟩ | ⟨-, rfl, ht⟩
  · omega
  exact ⟨t, hb, hreads, by rw [ht, calcOut_eq _ _ hlen]; rfl⟩

/-- A message `neg a`, for Lean's text of an integer `a`, makes the program write the line `0`, a
space, and Lean's text of `-a`. -/
theorem calc_unary (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) (x : ℤ)
    (hmsg : inMsg σ = ascii ("neg " ++ toString x)) (hmax : (inMsg σ).length ≤ msgMax) :
    ∃ t : trace, bigstep_program_terminates A X
        (inProgram pre messageCompiled.translation (inMain nativeCap 44 .array)) t 0 ∧
      Reads σ t ∧ t = inTrace σ 0 (8 + (inLen σ).toNat) ++
        outTrace (encodeWord (UInt64.ofNat (((ascii ("0 " ++ toString (-x))).length + 7) / 8)) ++
          ascii ("0 " ++ toString (-x)) ++
          List.replicate (((ascii ("0 " ++ toString (-x))).length + 7) / 8 * 8 -
            (ascii ("0 " ++ toString (-x))).length) 0) := by
  have hc : calcSpec (inMsg σ) = ascii ("0 " ++ toString (-x)) := by
    rw [hmsg]; exact calcSpec_unary x (by rw [← hmsg]; exact hmax)
  obtain ⟨t, hb, hr, ht⟩ := calc_line A X pre hpre σ (inLen_le_of_msgMax hmax)
  exact ⟨t, hb, hr, by rw [ht, hc]⟩

/-- A message `name a b`, for a binary operation of `binaryOps` and Lean's texts of integers `a`
and `b`, makes the program write the line `0`, a space, and Lean's text of the operation's exact
result, unless the operation divides and `b` is 0. -/
theorem calc_binary (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) (name : String) (division : Bool)
    (f : ℤ → ℤ → ℤ) (hop : (name, division, f) ∈ binaryOps) (x y : ℤ)
    (hdiv : ¬ (division = true ∧ y = 0))
    (hmsg : inMsg σ = ascii (name ++ " " ++ toString x ++ " " ++ toString y))
    (hmax : (inMsg σ).length ≤ msgMax) :
    ∃ t : trace, bigstep_program_terminates A X
        (inProgram pre messageCompiled.translation (inMain nativeCap 44 .array)) t 0 ∧
      Reads σ t ∧ t = inTrace σ 0 (8 + (inLen σ).toNat) ++
        outTrace (encodeWord (UInt64.ofNat (((ascii ("0 " ++ toString (f x y))).length + 7) / 8)) ++
          ascii ("0 " ++ toString (f x y)) ++
          List.replicate (((ascii ("0 " ++ toString (f x y))).length + 7) / 8 * 8 -
            (ascii ("0 " ++ toString (f x y))).length) 0) := by
  have hc : calcSpec (inMsg σ) = ascii ("0 " ++ toString (f x y)) := by
    rw [hmsg]; exact calcSpec_binary name division f hop x y hdiv (by rw [← hmsg]; exact hmax)
  obtain ⟨t, hb, hr, ht⟩ := calc_line A X pre hpre σ (inLen_le_of_msgMax hmax)
  exact ⟨t, hb, hr, by rw [ht, hc]⟩

/-- A message `name a 0`, for a division of `binaryOps` and Lean's text of an integer `a`, makes
the program write the line `3`. -/
theorem calc_zero_divisor (A : Archi) (X : ExtSem)
    (pre : List (ident × globdef (fundef function) type)) (hpre : PrefixOk pre)
    (σ : Nat → int) (name : String) (f : ℤ → ℤ → ℤ)
    (hop : (name, true, f) ∈ binaryOps) (x : ℤ)
    (hmsg : inMsg σ = ascii (name ++ " " ++ toString x ++ " 0"))
    (hmax : (inMsg σ).length ≤ msgMax) :
    ∃ t : trace, bigstep_program_terminates A X
        (inProgram pre messageCompiled.translation (inMain nativeCap 44 .array)) t 0 ∧
      Reads σ t ∧ t = inTrace σ 0 (8 + (inLen σ).toNat) ++
        outTrace (encodeWord 1 ++ ascii "3" ++ List.replicate 7 0) := by
  have hc : calcSpec (inMsg σ) = ascii "3" := by
    rw [hmsg]; exact calcSpec_zero_divisor name f hop x (by rw [← hmsg]; exact hmax)
  obtain ⟨t, hb, hr, ht⟩ := calc_line A X pre hpre σ (inLen_le_of_msgMax hmax)
  exact ⟨t, hb, hr, by rw [ht, hc]; rfl⟩

#print axioms calc_program
#print axioms calc_line
#print axioms calc_unary
#print axioms calc_binary
#print axioms calc_zero_divisor

end Demos.BignumCalc
