import LeanExe.A64.Proof.Machine

/-!
The bytes of generated code in an image.  `imageBytes` lays out each instruction's word with its
lowest byte first, the order in which the processor reads an instruction from memory, and
`fetchFrom` reads the words of a region of memory as the model's map of code words.
`codeAt_fetchFrom` states that a memory that holds the bytes of `is` from `a` gives a map of code
words that holds `is` at `a`, the premise `CodeAt` of the simulation's theorems.
-/

namespace LeanExe.A64

/-- The four bytes of a word, the lowest first. -/
def wordBytes (w : UInt32) : List UInt8 :=
  [w.toUInt8, (w >>> 8).toUInt8, (w >>> 16).toUInt8, (w >>> 24).toUInt8]

/-- The bytes of the instructions `is`, each word's lowest byte first. -/
def imageBytes (is : List Instr) : List UInt8 :=
  is.flatMap fun i => wordBytes (encode i)

/-- The word whose four bytes, the lowest first, are those of `m` from `a`. -/
def load32 (m : UInt64 → UInt8) (a : UInt64) : UInt32 :=
  UInt32.ofNat ((m a).toNat + (m (a + 1)).toNat * 2 ^ 8 + (m (a + 2)).toNat * 2 ^ 16 +
    (m (a + 3)).toNat * 2 ^ 24)

/-- The map of code words of the `n` words of `m` from `a`. -/
def fetchFrom (m : UInt64 → UInt8) (a : UInt64) (n : Nat) : UInt64 → Option UInt32 :=
  fun p => if (p - a).toNat < 4 * n ∧ (p - a).toNat % 4 = 0 then some (load32 m p) else none

theorem length_imageBytes (is : List Instr) : (imageBytes is).length = 4 * is.length := by
  induction is with
  | nil => rfl
  | cons i is ih =>
      simp only [imageBytes, List.flatMap_cons, List.length_append] at ih ⊢
      rw [ih]
      simp [wordBytes]
      omega

theorem getElem_imageBytes (is : List Instr) (i k : Nat) (hi : i < is.length) (hk : k < 4) :
    (imageBytes is)[4 * i + k]'(by rw [length_imageBytes]; omega) =
      (wordBytes (encode is[i]))[k]'(by simp [wordBytes]; omega) := by
  induction is generalizing i with
  | nil => simp at hi
  | cons j is ih =>
      cases i with
      | zero =>
          simp only [imageBytes, List.flatMap_cons]
          rw [List.getElem_append_left (by simp [wordBytes]; omega)]
          simp
      | succ i =>
          simp only [imageBytes, List.flatMap_cons]
          rw [List.getElem_append_right (by simp [wordBytes]; omega)]
          have := ih i (by simpa using hi)
          simp only [imageBytes] at this
          simp only [List.getElem_cons_succ]
          rw [← this]
          congr 1
          simp [wordBytes]
          omega

theorem load32_wordBytes {m : UInt64 → UInt8} {p : UInt64} {w : UInt32}
    (h : ∀ k (hk : k < 4),
      m (p + UInt64.ofNat k) = (wordBytes w)[k]'(by simp [wordBytes]; omega)) :
    load32 m p = w := by
  have h0 := h 0 (by decide)
  have h1 := h 1 (by decide)
  have h2 := h 2 (by decide)
  have h3 := h 3 (by decide)
  rw [show p + UInt64.ofNat 0 = p by simp] at h0
  simp only [wordBytes, List.getElem_cons_zero, List.getElem_cons_succ] at h0 h1 h2 h3
  unfold load32
  rw [show p + 1 = p + UInt64.ofNat 1 from rfl, show p + 2 = p + UInt64.ofNat 2 from rfl,
    show p + 3 = p + UInt64.ofNat 3 from rfl, h0, h1, h2, h3]
  apply UInt32.toNat_inj.mp
  have hw := w.toNat_lt
  simp only [UInt32.toNat_ofNat', UInt32.toNat_toUInt8, UInt32.toNat_shiftRight,
    Nat.shiftRight_eq_div_pow]
  have e8 : (8 : UInt32).toNat = 8 := rfl
  have e16 : (16 : UInt32).toNat = 16 := rfl
  have e24 : (24 : UInt32).toNat = 24 := rfl
  rw [e8, e16, e24]
  simp only [Nat.reducePow, Nat.reduceMod] at *
  omega

/-- A memory that holds the bytes of `is` from `a` gives a map of code words that holds `is` at
`a`. -/
theorem codeAt_fetchFrom {m : UInt64 → UInt8} {a : UInt64} {is : List Instr}
    (hn : 4 * is.length < 2 ^ 64)
    (hm : ∀ j (hj : j < (imageBytes is).length), m (a + UInt64.ofNat j) = (imageBytes is)[j]) :
    CodeAt (fetchFrom m a is.length) a is := by
  intro i hi
  have hd : (after a i - a).toNat = 4 * i := by
    rw [after, UInt64.add_comm, UInt64.add_sub_cancel, UInt64.toNat_mul, UInt64.toNat_ofNat']
    have e4 : (4 : UInt64).toNat = 4 := rfl
    rw [e4]
    simp only [Nat.reducePow] at hn ⊢
    omega
  simp only [fetchFrom, hd]
  rw [if_pos ⟨by omega, by omega⟩]
  congr 1
  apply load32_wordBytes
  intro k hk
  have := hm (4 * i + k) (by rw [length_imageBytes]; omega)
  rw [getElem_imageBytes is i k hi hk] at this
  rw [← this]
  congr 1
  rw [after, UInt64.add_assoc]
  congr 1
  rw [UInt64.ofNat_add, UInt64.ofNat_mul]
  rfl

end LeanExe.A64
