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

/-- Element `k` of the Wasm array in buffer `b`, or 0 when `k` is not below the length `len`,
for `vec2<u32>` variables `k` and `len`: the index is clamped into the buffer, so the access is
always in bounds. -/
def readLow (b k len : Nat) : Expr :=
  .select (.lit 0)
    (.index b (.min (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1))))
    (.bin .and (lt64 k len) (.bin .lt (.fst k) (.bin .div (.bin .sub (.length b) (.lit 2)) (.lit 2))))

theorem readLow_eval (ctx : Context) (env : Env) (b k len : Nat) (klo : UInt32) (n : Nat)
    (buf : Array UInt32) (hbuf : ctx.inputs[b]? = some buf) (hsize : buf.size = 2 + 2 * n)
    (hn : n < 2 ^ 31)
    (hk : env.find k = some (.vec2 klo 0, false))
    (hl : env.find len = some (.vec2 (UInt32.ofNat n) 0, false)) :
    (readLow b k len).eval ctx env =
      some (.u32 (if klo.toNat < n then buf[2 + 2 * klo.toNat]! else 0)) := by
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
  have hidx : (2 + 2 * klo).toNat = (2 + 2 * klo.toNat) % 2 ^ 32 := by
    rw [UInt32.toNat_add, UInt32.toNat_mul]
    simp only [UInt32.reduceToNat]
    omega
  -- The clamped index is inside the buffer, and it is element `klo`'s when `klo` is in range.
  set m : UInt32 := if 2 + 2 * klo ≤ UInt32.ofNat buf.size - 1 then 2 + 2 * klo
    else UInt32.ofNat buf.size - 1 with hm
  have hmIn : m.toNat < buf.size := by
    rw [hm]
    split
    · rename_i h
      rw [UInt32.le_iff_toNat_le, hlast] at h
      omega
    · omega
  have hmEl : klo.toNat < n → m.toNat = 2 + 2 * klo.toNat := by
    intro h
    rw [hm, ite_eq_left_iff.mpr (by intro h'; exact absurd (by rw [UInt32.le_iff_toNat_le, hlast, hidx]; omega) h'), hidx]
    omega
  have hminEval : (Expr.min (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1))).eval ctx env = some (.u32 m) := by
    simp [Expr.eval, hk, hbuf, BinOp.apply, hm]
  have hindex : (Expr.index b (.min (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1)))).eval ctx env = some (.u32 buf[m.toNat]) := by
    generalize (Expr.min (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst k)))
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
  unfold readLow
  generalize (Expr.index b (.min (.bin .add (.lit 2) (.bin .mul (.lit 2) (.fst k)))
      (.bin .sub (.length b) (.lit 1)))) = ti at hindex ⊢
  generalize (Expr.bin .and (lt64 k len)
      (.bin .lt (.fst k) (.bin .div (.bin .sub (.length b) (.lit 2)) (.lit 2)))) = tc at hcond ⊢
  simp only [Expr.eval, hindex, hcond]
  by_cases h : klo.toNat < n
  · simp [Value.sameType, h, hmEl h, getElem!_pos buf (2 + 2 * klo.toNat) (by omega)]
  · simp [Value.sameType, h]

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
