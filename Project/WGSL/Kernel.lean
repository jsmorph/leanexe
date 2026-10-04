import Project.WGSL.Semantics
import Project.ProofKit.F32Bits

/-!
Lemmas that kernels share: the 32-bit words of a Wasm array of 64-bit words, the comparison of
`u64` values held as `vec2<u32>` pairs, and the read of an element of a Wasm array held in a
buffer, which returns 0 for an index at or beyond the length and never leaves the buffer.
-/

namespace Project.WGSL

/-- Half of a 64-bit word: the least significant half, or the most significant. -/
def wordHalf (w : UInt64) (high : Bool) : UInt32 := if high then (w >>> 32).toUInt32 else w.toUInt32

/-- The 32-bit words of a Wasm array of 64-bit words: its length word, then each element, each
least significant half first. -/
def arrayWords (xs : Array UInt64) : Array UInt32 :=
  Array.ofFn (n := 2 + 2 * xs.size) fun i =>
    if i.val < 2 then wordHalf (UInt64.ofNat xs.size) (i.val = 1)
    else wordHalf xs[(i.val - 2) / 2]! (i.val % 2 = 1)

/-- `lt64 a b` for the `vec2<u32>` variables `a` and `b`: the 64-bit comparison of their pairs. -/
def lt64 (a b : Nat) : Expr :=
  .bin .or (.bin .lt (.snd a) (.snd b))
    (.bin .and (.bin .eq (.snd a) (.snd b)) (.bin .lt (.fst a) (.fst b)))

theorem arrayWords_size (xs : Array UInt64) : (arrayWords xs).size = 2 + 2 * xs.size := by
  simp [arrayWords]

theorem arrayWords_get (xs : Array UInt64) (i : Nat) (h : i < 2 + 2 * xs.size) :
    (arrayWords xs)[i]? = some (if i < 2 then wordHalf (UInt64.ofNat xs.size) (i = 1)
      else wordHalf xs[(i - 2) / 2]! (i % 2 = 1)) := by
  simp [arrayWords, h]

theorem lt64_eval (ctx : Context) (env : Env) (a b : Nat) (x y : UInt32)
    (ha : env.find a = some (.vec2 x 0, false)) (hb : env.find b = some (.vec2 y 0, false)) :
    (lt64 a b).eval ctx env = some (.bool (decide (x < y))) := by
  simp [lt64, Expr.eval, ha, hb, BinOp.apply]

/-- Word `base + 2k` of buffer `b`, or 0 when `k` is not below the length `len`, for `vec2<u32>`
variables `k` and `len`: with `base` 2, the low half of element `k` of the Wasm array the buffer
holds, and with `base` 3 its high half.  The index is clamped into the buffer, so the access never
leaves it. -/
def readAt (b k len : Nat) (base : UInt32) : Expr :=
  .select (.lit 0)
    (.index b (.min (.bin .add (.lit base) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1))))
    (.bin .and (lt64 k len) (.bin .lt (.fst k) (.bin .div (.bin .sub (.length b) (.lit 2)) (.lit 2))))

/-- The low half of element `k`. -/
abbrev readLow (b k len : Nat) : Expr := readAt b k len 2

/-- The high half of element `k`. -/
abbrev readHigh (b k len : Nat) : Expr := readAt b k len 3

theorem readAt_eval (ctx : Context) (env : Env) (b k len : Nat) (base : UInt32)
    (hbase : 2 ≤ base.toNat ∧ base.toNat ≤ 3) (klo : UInt32) (n : Nat)
    (buf : Array UInt32) (hbuf : ctx.inputs[b]? = some buf) (hsize : buf.size = 2 + 2 * n)
    (hn : n < 2 ^ 31)
    (hk : env.find k = some (.vec2 klo 0, false))
    (hl : env.find len = some (.vec2 (UInt32.ofNat n) 0, false)) :
    (readAt b k len base).eval ctx env =
      some (.u32 (if klo.toNat < n then buf[base.toNat + 2 * klo.toNat]! else 0)) := by
  have hklo := klo.toNat_lt
  have hlt := lt64_eval ctx env k len klo (UInt32.ofNat n) hk hl
  have hcmp : decide (klo < UInt32.ofNat n) = decide (klo.toNat < n) := by
    simp only [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt (by omega)]
  have hlast : (UInt32.ofNat buf.size - 1).toNat = 1 + 2 * n := by
    rw [hsize, UInt32.toNat_sub, UInt32.toNat_ofNat']
    simp only [UInt32.reduceToNat]
    omega
  have hhalf : ((UInt32.ofNat buf.size - 2) / 2).toNat = n := by
    rw [hsize, UInt32.toNat_div, UInt32.toNat_sub, UInt32.toNat_ofNat']
    simp only [UInt32.reduceToNat]
    omega
  have hidx : (base + 2 * klo).toNat = (base.toNat + 2 * klo.toNat) % 2 ^ 32 := by
    rw [UInt32.toNat_add, UInt32.toNat_mul]
    simp only [UInt32.reduceToNat]
    omega
  -- The clamped index is inside the buffer, and it is element `klo`'s when `klo` is in range.
  set m : UInt32 := if base + 2 * klo ≤ UInt32.ofNat buf.size - 1 then base + 2 * klo
    else UInt32.ofNat buf.size - 1 with hm
  have hmIn : m.toNat < buf.size := by
    rw [hm]
    split
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hlast] at h
      omega
    · omega
  have hmEl : klo.toNat < n → m.toNat = base.toNat + 2 * klo.toNat := by
    intro h
    rw [hm, ite_eq_left_iff.mpr (by intro h'; exact absurd (by rw [UInt32.le_iff_toNat_le, hlast, hidx]; omega) h'), hidx]
    omega
  have hminEval : (Expr.min (.bin .add (.lit base) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1))).eval ctx env = some (.u32 m) := by
    simp [Expr.eval, hk, hbuf, BinOp.apply, hm]
  have hindex : (Expr.index b (.min (.bin .add (.lit base) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1)))).eval ctx env = some (.u32 buf[m.toNat]) := by
    generalize (Expr.min (.bin .add (.lit base) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1))) = p at hminEval ⊢
    simp [Expr.eval, hbuf, hminEval, hmIn]
  have hcond : (Expr.bin .and (lt64 k len)
      (.bin .lt (.fst k) (.bin .div (.bin .sub (.length b) (.lit 2)) (.lit 2)))).eval ctx env =
      some (.bool (decide (klo.toNat < n))) := by
    simp only [Expr.eval, hlt, hcmp]
    by_cases h : klo.toNat < n
    · have : klo < (UInt32.ofNat buf.size - 2) / 2 := by
        rw [UInt32.lt_iff_toNat_lt, hhalf]; exact h
      simp [h, Expr.eval, hk, hbuf, BinOp.apply, this]
    · simp [h]
  unfold readAt
  generalize (Expr.index b (.min (.bin .add (.lit base) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1)))) = ti at hindex ⊢
  generalize (Expr.bin .and (lt64 k len)
      (.bin .lt (.fst k) (.bin .div (.bin .sub (.length b) (.lit 2)) (.lit 2)))) = tc at hcond ⊢
  simp only [Expr.eval, hindex, hcond]
  by_cases h : klo.toNat < n
  · simp [Value.sameType, h, hmEl h, getElem!_pos buf (base.toNat + 2 * klo.toNat) (by omega)]
  · simp [Value.sameType, h]

theorem readLow_eval (ctx : Context) (env : Env) (b k len : Nat) (klo : UInt32) (n : Nat)
    (buf : Array UInt32) (hbuf : ctx.inputs[b]? = some buf) (hsize : buf.size = 2 + 2 * n)
    (hn : n < 2 ^ 31)
    (hk : env.find k = some (.vec2 klo 0, false))
    (hl : env.find len = some (.vec2 (UInt32.ofNat n) 0, false)) :
    (readLow b k len).eval ctx env =
      some (.u32 (if klo.toNat < n then buf[2 + 2 * klo.toNat]! else 0)) :=
  readAt_eval ctx env b k len 2 (by decide) klo n buf hbuf hsize hn hk hl

/-- The halves of a 64-bit word as a `vec2<u32>` value. -/
def pairOf (w : UInt64) : Value := .vec2 w.toUInt32 (w >>> 32).toUInt32

theorem toNat_of_halves (w : UInt64) :
    w.toNat = (w >>> 32).toUInt32.toNat * 2 ^ 32 + w.toUInt32.toNat := by
  have := w.toNat_lt
  simp only [UInt64.toNat_toUInt32, UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    UInt64.reduceToNat, Nat.reduceMod]
  omega

/-- The comparison of two `u64` values held as their halves. -/
theorem lt64_word (ctx : Context) (env : Env) (a b : Nat) (x y : UInt64)
    (ha : env.find a = some (pairOf x, false)) (hb : env.find b = some (pairOf y, false)) :
    (lt64 a b).eval ctx env = some (.bool (decide (x < y))) := by
  have hx := toNat_of_halves x
  have hy := toNat_of_halves y
  have hxl := x.toUInt32.toNat_lt
  have hyl := y.toUInt32.toNat_lt
  have key : decide (x < y) = (decide ((x >>> 32).toUInt32 < (y >>> 32).toUInt32) ||
      (((x >>> 32).toUInt32 == (y >>> 32).toUInt32) && decide (x.toUInt32 < y.toUInt32))) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      UInt64.lt_iff_toNat_lt, UInt32.lt_iff_toNat_lt]
    constructor
    · intro h
      by_cases hh : (x >>> 32).toUInt32.toNat < (y >>> 32).toUInt32.toNat
      · exact Or.inl hh
      · exact Or.inr ⟨UInt32.toNat_inj.mp (by omega), by omega⟩
    · rintro (h | ⟨h, h'⟩)
      · omega
      · have := congrArg UInt32.toNat h
        omega
  rw [key]
  simp only [pairOf] at ha hb
  generalize (x >>> 32).toUInt32 = xh at ha ⊢
  generalize x.toUInt32 = xl at ha ⊢
  generalize (y >>> 32).toUInt32 = yh at hb ⊢
  generalize y.toUInt32 = yl at hb ⊢
  cases h1 : decide (xh < yh) <;> cases h2 : (xh == yh) <;> cases h3 : decide (xl < yl) <;>
    simp [lt64, Expr.eval, ha, hb, BinOp.apply, h1, h2, h3]

theorem readAt_eval_high (ctx : Context) (env : Env) (b k len : Nat) (base : UInt32)
    (klo khi : UInt32) (n : Nat) (buf : Array UInt32) (hbuf : ctx.inputs[b]? = some buf)
    (hsize : buf.size = 2 + 2 * n) (hn : n < 2 ^ 31) (hhi : khi ≠ 0)
    (hk : env.find k = some (.vec2 klo khi, false))
    (hl : env.find len = some (.vec2 (UInt32.ofNat n) 0, false)) :
    (readAt b k len base).eval ctx env = some (.u32 0) := by
  have hlast : (UInt32.ofNat buf.size - 1).toNat = 1 + 2 * n := by
    rw [hsize, UInt32.toNat_sub, UInt32.toNat_ofNat']
    simp only [UInt32.reduceToNat]
    omega
  set m : UInt32 := if base + 2 * klo ≤ UInt32.ofNat buf.size - 1 then base + 2 * klo
    else UInt32.ofNat buf.size - 1 with hm
  have hmIn : m.toNat < buf.size := by
    rw [hm]
    split
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hlast] at h
      omega
    · omega
  have hnot0 : ¬ khi < 0 := by simp [UInt32.lt_iff_toNat_lt]
  have hne : (khi == 0) = false := by simpa using hhi
  simp [readAt, lt64, Expr.eval, hk, hl, hbuf, BinOp.apply, hnot0, hne, ← hm, hmIn,
    Value.sameType]

/-- The read of element `k`, any `u64` held as its halves, of a Wasm array in a buffer: base 2
gives the low half of `xs[k.toNat]!` and base 3 its high half, as `Expr.readValue_at` gives the
word. -/
theorem readAt_word (ctx : Context) (env : Env) (b kv len : Nat) (xs : Array UInt64)
    (hn : xs.size < 2 ^ 29) (k : UInt64) (high : Bool)
    (hbuf : ctx.inputs[b]? = some (arrayWords xs))
    (hk : env.find kv = some (pairOf k, false))
    (hl : env.find len = some (.vec2 (UInt32.ofNat xs.size) 0, false)) :
    (readAt b kv len (if high then 3 else 2)).eval ctx env =
      some (.u32 (wordHalf xs[k.toNat]! high)) := by
  have hsize := arrayWords_size xs
  simp only [pairOf] at hk
  have hbase : 2 ≤ (if high then (3 : UInt32) else 2).toNat ∧
      (if high then (3 : UInt32) else 2).toNat ≤ 3 := by cases high <;> decide
  have hbaseNat : (if high then (3 : UInt32) else 2).toNat = if high then 3 else 2 := by
    cases high <;> rfl
  by_cases hhi : (k >>> 32).toUInt32 = 0
  · rw [hhi] at hk
    have hk32 : k.toNat < 2 ^ 32 := by
      have := toNat_of_halves k
      rw [hhi] at this
      have := k.toUInt32.toNat_lt
      simp at *; omega
    have hlo : k.toUInt32.toNat = k.toNat := by
      simp [UInt64.toNat_toUInt32]; omega
    rw [readAt_eval ctx env b kv len _ hbase k.toUInt32 xs.size _ hbuf hsize (by omega) hk hl,
      hlo, hbaseNat]
    by_cases hlt : k.toNat < xs.size
    · rw [if_pos hlt, getElem!_pos (arrayWords xs) _ (by cases high <;> simp <;> omega)]
      have := arrayWords_get xs ((if high then 3 else 2) + 2 * k.toNat)
        (by cases high <;> simp <;> omega)
      rw [Array.getElem?_eq_getElem (by cases high <;> simp <;> omega)] at this
      rw [Option.some.inj this, if_neg (by cases high <;> simp <;> omega)]
      have hd : ((if high then 3 else 2) + 2 * k.toNat - 2) / 2 = k.toNat := by
        cases high <;> simp <;> omega
      rw [hd]
      cases high
      · have hm : ¬((2 + 2 * k.toNat) % 2 = 1) := by omega
        simp [hm]
      · have hm : (3 + 2 * k.toNat) % 2 = 1 := by omega
        simp [hm]
    · rw [if_neg hlt, getElem!_neg xs _ hlt]
      cases high <;> rfl
  · rw [readAt_eval_high ctx env b kv len _ k.toUInt32 _ xs.size _ hbuf hsize (by omega) hhi hk hl]
    have hbig : xs.size ≤ k.toNat := by
      have := toNat_of_halves k
      have : (k >>> 32).toUInt32.toNat ≠ 0 := fun h => hhi (UInt32.toNat_inj.mp h)
      omega
    rw [getElem!_neg xs _ (by omega)]
    cases high <;> rfl

theorem foldlM_some {α β : Type} (f : β → α → Option β) (g : β → α → β) (l : List α)
    (h : ∀ b, ∀ a ∈ l, f b a = some (g b a)) (init : β) :
    l.foldlM f init = some (l.foldl g init) := by
  induction l generalizing init with
  | nil => rfl
  | cons a l ih =>
      simp only [List.foldlM, h init a (by simp), List.foldl_cons]
      exact ih (fun b a' ha' => h b a' (by simp [ha'])) _

theorem arrayWords_floats (x : Array Float32) (hSize : 2 + 2 * x.size < 2 ^ 32) :
    (arrayWords (x.map fun v => v.toBits.toUInt64))[0]? = some (UInt32.ofNat x.size) ∧
    (arrayWords (x.map fun v => v.toBits.toUInt64))[1]? = some 0 ∧
    (arrayWords (x.map fun v => v.toBits.toUInt64)).size = 2 + 2 * x.size ∧
    ∀ k, k < x.size →
      (arrayWords (x.map fun v => v.toBits.toUInt64))[2 + 2 * k]? = some x[k]!.toBits := by
  refine ⟨?_, ?_, by simp [arrayWords_size], fun k hk => ?_⟩
  · rw [arrayWords_get _ 0 (by simp)]
    simp [wordHalf]
  · rw [arrayWords_get _ 1 (by simp; omega)]
    simp only [wordHalf, Array.size_map]
    simp
    apply UInt32.toNat_inj.mp
    simp [UInt64.toNat_shiftRight]
    omega
  · rw [arrayWords_get _ _ (by rw [Array.size_map]; omega), if_neg (by omega)]
    have hd : (2 + 2 * k - 2) / 2 = k := by omega
    have hm : ¬((2 + 2 * k) % 2 = 1) := by omega
    rw [hd]
    simp [hm, wordHalf, getElem!_pos x k hk, hk]

end Project.WGSL
