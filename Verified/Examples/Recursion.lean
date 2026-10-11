import Verified.Reflect.Command

/-! The twenty-first program of the verified compiler: recursion.  Each definition recurses by
well-founded recursion on a word measure, and its meaning is the definition itself, which solves
the fixed-point equation of its body.  The code of a recursive function, and of a function that
calls one, takes the call depth and traps at `unreachable` at depth 1,000; the theorem for it holds
at its exported entry, which starts at depth 0.  The programs recurse once and twice per call, on
words, floats, a pair, a structure, an array of structures, and an owned array that each call
extends and moves into the next, and one calls two of the others. -/

namespace Verified.Examples.Recursion

open LeanExe.Pipeline

/-- Euclid's algorithm. -/
def gcd (a b : UInt64) : UInt64 :=
  if b = 0 then a else gcd b (a % b)
termination_by b.toNat
decreasing_by
  rename_i h
  have hb : b.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
  simp_wf
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

/-- `b ^ e` modulo `2 ^ 64`, by squaring.  The `if h :` gives the termination proof its
hypothesis by name. -/
def pow (b e : UInt64) : UInt64 :=
  if h : e = 0 then 1
  else
    let half := pow (b * b) (e / 2)
    if e % 2 = 0 then half else b * half
termination_by e.toNat
decreasing_by
  have he : e.toNat ≠ 0 := fun e' => h (UInt64.toNat_inj.mp (by simpa using e'))
  simp_wf
  omega

/-- The sum of the elements of `xs` from `lo` up to `hi`, by halves. -/
def sumRange (xs : Array Float) (lo hi : UInt64) : Float :=
  if hi - lo ≤ 1 then (if hi - lo = 1 then xs[lo.toNat]! else 0.0)
  else
    let mid := lo + (hi - lo) / 2
    sumRange xs lo mid + sumRange xs mid hi
termination_by (hi - lo).toNat
decreasing_by
  all_goals
    rename_i h
    have := UInt64.toNat_lt lo
    have := UInt64.toNat_lt hi
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_sub, UInt64.toNat_add, UInt64.toNat_div,
      UInt64.reduceToNat] at h ⊢
    omega

/-- `xs` extended by the words from `i` up to `n`. -/
def fill (xs : Array UInt64) (i n : UInt64) : Array UInt64 :=
  if i < n then fill (xs.push i) (i + 1) n else xs
termination_by (n - i).toNat
decreasing_by
  rename_i h
  have := UInt64.toNat_lt i
  have := UInt64.toNat_lt n
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    at h ⊢
  omega

/-- `n`, by `n` nested calls: it returns at `n = 999` and traps at `n = 1000`. -/
def chain (n : UInt64) : UInt64 := if n = 0 then 0 else chain (n - 1) + 1
termination_by n.toNat
decreasing_by
  rename_i h
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at h ⊢
  omega

/-- The pair of Fibonacci numbers `k` steps after `p`. -/
def fibPair (p : UInt64 × UInt64) (k : UInt64) : UInt64 × UInt64 :=
  if k = 0 then p else fibPair (p.2, p.1 + p.2) (k - 1)
termination_by k.toNat
decreasing_by
  rename_i h
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at h ⊢
  omega

structure Point where
  x : UInt64
  y : UInt64
  deriving Inhabited

instance : Flat Point (UInt64 × UInt64) := ⟨fun p => (p.x, p.y)⟩

/-- `p` after `k` steps that add `y` to `x` and 1 to `y`. -/
def walk (p : Point) (k : UInt64) : Point :=
  if k = 0 then p else walk ⟨p.x + p.y, p.y + 1⟩ (k - 1)
termination_by k.toNat
decreasing_by
  rename_i h
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at h ⊢
  omega

/-- The sum of the `x` fields of the points of `ps` from `i` on. -/
def sumXs (ps : Array Point) (i : UInt64) : UInt64 :=
  if i < ps.size.toUInt64 then ps[i.toNat]!.x + sumXs ps (i + 1) else 0
termination_by (ps.size.toUInt64 - i).toNat
decreasing_by
  rename_i h
  have := UInt64.toNat_lt i
  have := UInt64.toNat_lt ps.size.toUInt64
  simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub, UInt64.toNat_add, UInt64.reduceToNat]
    at h ⊢
  omega

/-- A function without recursion that calls two recursive ones, so that its code takes the call
depth too. -/
def powGcd (a b : UInt64) : UInt64 := pow a (gcd a b) + gcd (pow b 2) a

/-- Two functions without recursion, each with many values live, which `deep` calls at its
deepest frame. -/
def top2 (a b : UInt64) : UInt64 :=
  let x0 := a * b
  let x1 := x0 + b * 1
  let x2 := x1 + b * 2
  let x3 := x2 + b * 3
  let x4 := x3 + b * 4
  let x5 := x4 + b * 5
  let x6 := x5 + b * 6
  let x7 := x6 + b * 7
  let x8 := x7 + b * 8
  let x9 := x8 + b * 9
  let x10 := x9 + b * 10
  let x11 := x10 + b * 11
  let x12 := x11 + b * 12
  let x13 := x12 + b * 13
  let x14 := x13 + b * 14
  let x15 := x14 + b * 15
  let x16 := x15 + b * 16
  let x17 := x16 + b * 17
  let x18 := x17 + b * 18
  let x19 := x18 + b * 19
  let x20 := x19 + b * 20
  let x21 := x20 + b * 21
  let x22 := x21 + b * 22
  let x23 := x22 + b * 23
  let x24 := x23 + b * 24
  let x25 := x24 + b * 25
  x0 ^^^ x1 ^^^ x2 ^^^ x3 ^^^ x4 ^^^ x5 ^^^ x6 ^^^ x7 ^^^ x8 ^^^ x9 ^^^ x10 ^^^ x11 ^^^ x12 ^^^ x13
    ^^^ x14 ^^^ x15 ^^^ x16 ^^^ x17 ^^^ x18 ^^^ x19 ^^^ x20 ^^^ x21 ^^^ x22 ^^^ x23 ^^^ x24 ^^^ x25

def top1 (a b : UInt64) : UInt64 :=
  let x0 := a + b
  let x1 := x0 * b + 1
  let x2 := x1 * b + 2
  let x3 := x2 * b + 3
  let x4 := x3 * b + 4
  let x5 := x4 * b + 5
  let x6 := x5 * b + 6
  let x7 := x6 * b + 7
  let x8 := x7 * b + 8
  let x9 := x8 * b + 9
  let x10 := x9 * b + 10
  let x11 := x10 * b + 11
  let x12 := x11 * b + 12
  let x13 := x12 * b + 13
  let x14 := x13 * b + 14
  let x15 := x14 * b + 15
  let x16 := x15 * b + 16
  let x17 := x16 * b + 17
  let x18 := x17 * b + 18
  let x19 := x18 * b + 19
  let x20 := x19 * b + 20
  let x21 := x20 * b + 21
  let x22 := x21 * b + 22
  let x23 := x22 * b + 23
  let x24 := x23 * b + 24
  let x25 := x24 * b + 25
  top2 x0 x25 + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15
    + x16 + x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25

/-- A recursion whose frame has 32 positions, as many as the reflector accepts in a function
that takes the call depth, each holding a value live across the self-call, with `top1` and `top2`
at the top of the chain: at `n = 999` it runs 1,000 nested frames in Wasmtime's default stack. -/
def deep (n a b : UInt64) : UInt64 :=
  if n = 0 then top1 a b else
    let x0 := a + b
    let x1 := x0 * b + 1
    let x2 := x1 * b + 2
    let x3 := x2 * b + 3
    let x4 := x3 * b + 4
    let x5 := x4 * b + 5
    let x6 := x5 * b + 6
    let x7 := x6 * b + 7
    let x8 := x7 * b + 8
    let x9 := x8 * b + 9
    let x10 := x9 * b + 10
    let x11 := x10 * b + 11
    let x12 := x11 * b + 12
    let x13 := x12 * b + 13
    let x14 := x13 * b + 14
    let x15 := x14 * b + 15
    let x16 := x15 * b + 16
    let x17 := x16 * b + 17
    let x18 := x17 * b + 18
    let x19 := x18 * b + 19
    let x20 := x19 * b + 20
    let x21 := x20 * b + 21
    let x22 := x21 * b + 22
    let x23 := x22 * b + 23
    let x24 := x23 * b + 24
    let x25 := x24 * b + 25
    let r := deep (n - 1) b x25
    r + x0 + x1 + x2 + x3 + x4 + x5 + x6 + x7 + x8 + x9 + x10 + x11 + x12 + x13 + x14 + x15 + x16 +
      x17 + x18 + x19 + x20 + x21 + x22 + x23 + x24 + x25
termination_by n.toNat
decreasing_by
  rename_i h
  simp only [← UInt64.toNat_inj, UInt64.toNat_sub, UInt64.reduceToNat] at h ⊢
  omega

verified_compile compiled := [gcd, pow, sumRange, fill, chain, fibPair, walk, sumXs, powGcd,
  top2, top1, deep]

/-- `chain n` makes `n + 1` nested calls: with `k` frames available, its calls find their frames
exactly when `n < k`. -/
theorem chain_fits : ∀ (k : Nat) (n : UInt64), compiled.chain.fits k n = true ↔ n.toNat < k
  | 0, n => by simp [show compiled.chain.fits 0 n = false from rfl]
  | k + 1, n => by
    rw [compiled.chain.fits_eq]
    by_cases h : n = 0
    · simp [h]
    · simp only [h, ↓reduceIte, chain_fits k (n - 1)]
      have hn : n.toNat ≠ 0 := fun e => h (UInt64.toNat_inj.mp (by simpa using e))
      simp only [UInt64.toNat_sub, UInt64.reduceToNat]
      have := UInt64.toNat_lt n
      omega

/-- `chain` allocates nothing. -/
theorem chain_bound : ∀ (k : Nat) (n : UInt64), compiled.chain.bound k n = 0
  | 0, _ => rfl
  | k + 1, n => by
    rw [compiled.chain.bound_eq, chain_bound k]
    simp

/-- The module computes `chain n` without a trap for every `n` below 1,000, and leaves `top`
where it was. -/
theorem chain_trapFree : LeanExe.Pipeline.ImplementsA false compiled.module 18 (fun x => chain x)
    (fun x heap store => x.toNat < 1000 ∧ heap.Within store compiled.module 0)
    (fun _ heap _ heap' _ => heap'.top.toNat ≤ heap.top.toNat) :=
  compiled.chain.trapFree.mono
    (fun x _ _ h => ⟨(chain_fits 1000 x).mpr h.1, by rw [chain_bound]; exact h.2⟩)
    fun x _ _ _ _ _ h => by simpa [chain_bound] using h

end Verified.Examples.Recursion
