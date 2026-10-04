import Project.WGSL.Kernel

/-!
`u64` addition and multiplication on `vec2<u32>` pairs, least significant half first.  WGSL has
no high half of a 32-bit product, so `mulHigh` splits each operand into 16-bit halves with
division and multiplication by `65536u`.
-/

namespace Project.WGSL

/-- The sum of the pairs in variables `a` and `b`, with the carry of the low halves. -/
def add64 (a b : Nat) : Expr :=
  .vec2 (.bin .add (.fst a) (.fst b))
    (.bin .add (.bin .add (.snd a) (.snd b))
      (.select (.lit 0) (.lit 1) (.bin .lt (.bin .add (.fst a) (.fst b)) (.fst a))))

def hi16 (e : Expr) : Expr := .bin .div e (.lit 65536)

def lo16 (e : Expr) : Expr := .bin .sub e (.bin .mul (hi16 e) (.lit 65536))

/-- The high half of the 64-bit product of two `u32` values. -/
def mulHigh (x y : Expr) : Expr :=
  let p00 := Expr.bin .mul (lo16 x) (lo16 y)
  let p01 := Expr.bin .mul (lo16 x) (hi16 y)
  let p10 := Expr.bin .mul (hi16 x) (lo16 y)
  let p11 := Expr.bin .mul (hi16 x) (hi16 y)
  let mid := Expr.bin .add (.bin .add (hi16 p00) (lo16 p01)) (lo16 p10)
  .bin .add (.bin .add (.bin .add p11 (hi16 p01)) (hi16 p10)) (hi16 mid)

/-- The product of the pairs in variables `a` and `b`, modulo 2^64. -/
def mul64 (a b : Nat) : Expr :=
  .vec2 (.bin .mul (.fst a) (.fst b))
    (.bin .add (.bin .add (mulHigh (.fst a) (.fst b)) (.bin .mul (.fst a) (.snd b)))
      (.bin .mul (.snd a) (.fst b)))

theorem eval_u32_bin (ctx : Context) (env : Env) (op : BinOp) (l r : Expr) (x y : UInt32)
    (hop : op = .add ∨ op = .sub ∨ op = .mul ∨ op = .div)
    (hl : l.eval ctx env = some (.u32 x)) (hr : r.eval ctx env = some (.u32 y)) :
    (Expr.bin op l r).eval ctx env = (BinOp.apply op (.u32 x) (.u32 y)) := by
  rcases hop with rfl | rfl | rfl | rfl <;> simp [Expr.eval, hl, hr]

theorem eval_vec2 (ctx : Context) (env : Env) (l h : Expr) (x y : UInt32)
    (hl : l.eval ctx env = some (.u32 x)) (hh : h.eval ctx env = some (.u32 y)) :
    (Expr.vec2 l h).eval ctx env = some (.vec2 x y) := by
  simp [Expr.eval, hl, hh]

theorem eval_hi16 (ctx : Context) (env : Env) (e : Expr) (x : UInt32)
    (h : e.eval ctx env = some (.u32 x)) :
    (hi16 e).eval ctx env = some (.u32 (UInt32.ofNat (x.toNat / 65536))) := by
  rw [hi16, eval_u32_bin ctx env .div e _ x 65536 (by simp) h rfl]
  have h0 : (65536 : UInt32) ≠ 0 := by decide
  simp only [BinOp.apply, Option.some.injEq, Value.u32.injEq, h0, ↓reduceIte]
  apply UInt32.toNat_inj.mp
  have := x.toNat_lt
  simp only [UInt32.toNat_div, UInt32.reduceToNat, UInt32.toNat_ofNat']
  omega

theorem eval_lo16 (ctx : Context) (env : Env) (e : Expr) (x : UInt32)
    (h : e.eval ctx env = some (.u32 x)) :
    (lo16 e).eval ctx env = some (.u32 (UInt32.ofNat (x.toNat % 65536))) := by
  rw [lo16, eval_u32_bin ctx env .sub e _ x (UInt32.ofNat (x.toNat / 65536) * 65536) (by simp) h
    (by rw [eval_u32_bin ctx env .mul _ _ _ 65536 (by simp) (eval_hi16 ctx env e x h) rfl]; rfl)]
  simp only [BinOp.apply, Option.some.injEq, Value.u32.injEq]
  apply UInt32.toNat_inj.mp
  have := x.toNat_lt
  simp only [UInt32.toNat_sub, UInt32.toNat_mul, UInt32.toNat_ofNat', UInt32.reduceToNat]
  omega

/-- The high half of a product of 16-bit splits. -/
theorem mulHigh_nat (a0 a1 b0 b1 : Nat) :
    (a1 * 65536 + a0) * (b1 * 65536 + b0) / 4294967296 =
      a1 * b1 + a0 * b1 / 65536 + a1 * b0 / 65536 +
        (a0 * b0 / 65536 + a0 * b1 % 65536 + a1 * b0 % 65536) / 65536 := by
  have hexp : (a1 * 65536 + a0) * (b1 * 65536 + b0) =
      a1 * b1 * 4294967296 + (a0 * b1 + a1 * b0) * 65536 + a0 * b0 := by grind
  rw [hexp]
  generalize a1 * b1 = p11
  generalize a0 * b1 = p01
  generalize a1 * b0 = p10
  generalize a0 * b0 = p00
  omega

theorem mulHigh_eval (ctx : Context) (env : Env) (x y : Expr) (a b : UInt32)
    (hx : x.eval ctx env = some (.u32 a)) (hy : y.eval ctx env = some (.u32 b)) :
    (mulHigh x y).eval ctx env = some (.u32 (UInt32.ofNat (a.toNat * b.toNat / 4294967296))) := by
  have ha := a.toNat_lt
  have hb := b.toNat_lt
  have hx0 := eval_lo16 ctx env x a hx
  have hx1 := eval_hi16 ctx env x a hx
  have hy0 := eval_lo16 ctx env y b hy
  have hy1 := eval_hi16 ctx env y b hy
  generalize hA0 : UInt32.ofNat (a.toNat % 65536) = A0 at hx0
  generalize hA1 : UInt32.ofNat (a.toNat / 65536) = A1 at hx1
  generalize hB0 : UInt32.ofNat (b.toNat % 65536) = B0 at hy0
  generalize hB1 : UInt32.ofNat (b.toNat / 65536) = B1 at hy1
  have hp00 := eval_u32_bin ctx env .mul _ _ A0 B0 (by simp) hx0 hy0
  have hp01 := eval_u32_bin ctx env .mul _ _ A0 B1 (by simp) hx0 hy1
  have hp10 := eval_u32_bin ctx env .mul _ _ A1 B0 (by simp) hx1 hy0
  have hp11 := eval_u32_bin ctx env .mul _ _ A1 B1 (by simp) hx1 hy1
  simp only [BinOp.apply] at hp00 hp01 hp10 hp11
  have hq00 := eval_hi16 ctx env _ _ hp00
  have hq01 := eval_hi16 ctx env _ _ hp01
  have hq10 := eval_hi16 ctx env _ _ hp10
  have hr01 := eval_lo16 ctx env _ _ hp01
  have hr10 := eval_lo16 ctx env _ _ hp10
  have hmid1 := eval_u32_bin ctx env .add _ _ _ _ (by simp) hq00 hr01
  simp only [BinOp.apply] at hmid1
  have hmid := eval_u32_bin ctx env .add _ _ _ _ (by simp) hmid1 hr10
  simp only [BinOp.apply] at hmid
  have hqmid := eval_hi16 ctx env _ _ hmid
  have hs1 := eval_u32_bin ctx env .add _ _ _ _ (by simp) hp11 hq01
  simp only [BinOp.apply] at hs1
  have hs2 := eval_u32_bin ctx env .add _ _ _ _ (by simp) hs1 hq10
  simp only [BinOp.apply] at hs2
  have hs3 := eval_u32_bin ctx env .add _ _ _ _ (by simp) hs2 hqmid
  simp only [BinOp.apply] at hs3
  rw [mulHigh]
  rw [hs3]
  congr 2
  apply UInt32.toNat_inj.mp
  subst hA0 hA1 hB0 hB1
  have h0 : (UInt32.ofNat (a.toNat % 65536)).toNat = a.toNat % 65536 := by
    simp only [UInt32.toNat_ofNat']; omega
  have h1 : (UInt32.ofNat (a.toNat / 65536)).toNat = a.toNat / 65536 := by
    simp only [UInt32.toNat_ofNat']; omega
  have h2 : (UInt32.ofNat (b.toNat % 65536)).toNat = b.toNat % 65536 := by
    simp only [UInt32.toNat_ofNat']; omega
  have h3 : (UInt32.ofNat (b.toNat / 65536)).toNat = b.toNat / 65536 := by
    simp only [UInt32.toNat_ofNat']; omega
  have key := mulHigh_nat (a.toNat % 65536) (a.toNat / 65536) (b.toNat % 65536) (b.toNat / 65536)
  rw [show a.toNat / 65536 * 65536 + a.toNat % 65536 = a.toNat by omega,
    show b.toNat / 65536 * 65536 + b.toNat % 65536 = b.toNat by omega] at key
  have hlt00 : a.toNat % 65536 * (b.toNat % 65536) < 4294967296 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show a.toNat % 65536 < 65536 by omega)
      (show b.toNat % 65536 < 65536 by omega)
    omega
  have hlt01 : a.toNat % 65536 * (b.toNat / 65536) < 4294967296 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show a.toNat % 65536 < 65536 by omega)
      (show b.toNat / 65536 < 65536 by omega)
    omega
  have hlt10 : a.toNat / 65536 * (b.toNat % 65536) < 4294967296 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show a.toNat / 65536 < 65536 by omega)
      (show b.toNat % 65536 < 65536 by omega)
    omega
  have hlt11 : a.toNat / 65536 * (b.toNat / 65536) < 4294967296 := by
    have := Nat.mul_lt_mul_of_lt_of_lt (show a.toNat / 65536 < 65536 by omega)
      (show b.toNat / 65536 < 65536 by omega)
    omega
  have hprod : a.toNat * b.toNat < 4294967296 * 4294967296 :=
    Nat.mul_lt_mul_of_lt_of_lt ha hb
  simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat', h0, h1, h2, h3]
  generalize a.toNat % 65536 * (b.toNat % 65536) = p00 at *
  generalize a.toNat % 65536 * (b.toNat / 65536) = p01 at *
  generalize a.toNat / 65536 * (b.toNat % 65536) = p10 at *
  generalize a.toNat / 65536 * (b.toNat / 65536) = p11 at *
  generalize a.toNat * b.toNat = p at *
  omega

theorem add64_word (ctx : Context) (env : Env) {ma mb : Bool} (a b : Nat) (x y : UInt64)
    (ha : env.find a = some (pairOf x, ma)) (hb : env.find b = some (pairOf y, mb)) :
    (add64 a b).eval ctx env = some (pairOf (x + y)) := by
  have hx := toNat_of_halves x
  have hy := toNat_of_halves y
  have hs := toNat_of_halves (x + y)
  have hxl := x.toUInt32.toNat_lt
  have hyl := y.toUInt32.toNat_lt
  have hxh := (x >>> 32).toUInt32.toNat_lt
  have hyh := (y >>> 32).toUInt32.toNat_lt
  have hsl := (x + y).toUInt32.toNat_lt
  have hsh := ((x + y) >>> 32).toUInt32.toNat_lt
  have hsum : (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 64 := UInt64.toNat_add x y
  simp only [pairOf] at ha hb ⊢
  have hlow : (x.toUInt32 + y.toUInt32).toNat = (x.toUInt32.toNat + y.toUInt32.toNat) % 2 ^ 32 :=
    UInt32.toNat_add _ _
  by_cases h : 2 ^ 32 ≤ x.toUInt32.toNat + y.toUInt32.toNat
  · have hc : decide (x.toUInt32 + y.toUInt32 < x.toUInt32) = true := by
      simp only [decide_eq_true_eq, UInt32.lt_iff_toNat_lt, hlow]
      omega
    have hlt : x.toUInt32 + y.toUInt32 < x.toUInt32 := by simpa using hc
    simp [add64, Expr.eval, ha, hb, BinOp.apply, hlt, Value.sameType]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.reduceToNat]
    omega
  · have hc : decide (x.toUInt32 + y.toUInt32 < x.toUInt32) = false := by
      simp only [decide_eq_false_iff_not, UInt32.lt_iff_toNat_lt, hlow]
      omega
    have hlt : ¬ x.toUInt32 + y.toUInt32 < x.toUInt32 := by simpa using hc
    simp [add64, Expr.eval, ha, hb, BinOp.apply, hlt, Value.sameType]
    apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add]
    omega

/-- The 64-bit product of halves, modulo 2^64. -/
theorem mul64_nat (xh xl yh yl : Nat) :
    ((xh * 4294967296 + xl) * (yh * 4294967296 + yl)) % 18446744073709551616 / 4294967296 =
      (xl * yl / 4294967296 + xl * yh + xh * yl) % 4294967296 ∧
    ((xh * 4294967296 + xl) * (yh * 4294967296 + yl)) % 18446744073709551616 % 4294967296 =
      xl * yl % 4294967296 := by
  have hexp : (xh * 4294967296 + xl) * (yh * 4294967296 + yl) =
      xh * yh * 18446744073709551616 + (xl * yh + xh * yl) * 4294967296 + xl * yl := by grind
  rw [hexp]
  generalize xh * yh = phh
  generalize xl * yh = plh
  generalize xh * yl = phl
  generalize xl * yl = pll
  omega

theorem mul64_word (ctx : Context) (env : Env) {ma mb : Bool} (a b : Nat) (x y : UInt64)
    (ha : env.find a = some (pairOf x, ma)) (hb : env.find b = some (pairOf y, mb)) :
    (mul64 a b).eval ctx env = some (pairOf (x * y)) := by
  have hx := toNat_of_halves x
  have hy := toNat_of_halves y
  have hp := toNat_of_halves (x * y)
  have hprod : (x * y).toNat = (x.toNat * y.toNat) % 2 ^ 64 := UInt64.toNat_mul x y
  simp only [pairOf] at ha hb ⊢
  have hxl : (Expr.fst a).eval ctx env = some (.u32 x.toUInt32) := by simp [Expr.eval, ha]
  have hxh : (Expr.snd a).eval ctx env = some (.u32 (x >>> 32).toUInt32) := by
    simp [Expr.eval, ha]
  have hyl : (Expr.fst b).eval ctx env = some (.u32 y.toUInt32) := by simp [Expr.eval, hb]
  have hyh : (Expr.snd b).eval ctx env = some (.u32 (y >>> 32).toUInt32) := by
    simp [Expr.eval, hb]
  have hhigh := mulHigh_eval ctx env _ _ _ _ hxl hyl
  have hlo := eval_u32_bin ctx env .mul _ _ _ _ (by simp) hxl hyl
  have hc1 := eval_u32_bin ctx env .mul _ _ _ _ (by simp) hxl hyh
  have hc2 := eval_u32_bin ctx env .mul _ _ _ _ (by simp) hxh hyl
  simp only [BinOp.apply] at hlo hc1 hc2
  have hs1 := eval_u32_bin ctx env .add _ _ _ _ (by simp) hhigh hc1
  simp only [BinOp.apply] at hs1
  have hs2 := eval_u32_bin ctx env .add _ _ _ _ (by simp) hs1 hc2
  simp only [BinOp.apply] at hs2
  rw [mul64, eval_vec2 ctx env _ _ _ _ hlo hs2]
  simp only [Option.some.injEq, Value.vec2.injEq]
  have key := mul64_nat (x >>> 32).toUInt32.toNat x.toUInt32.toNat (y >>> 32).toUInt32.toNat
    y.toUInt32.toNat
  rw [show (2 : Nat) ^ 32 = 4294967296 from rfl] at hx hy hp
  rw [show (2 : Nat) ^ 64 = 18446744073709551616 from rfl] at hprod
  rw [← hx, ← hy, ← hprod] at key
  have hxll := x.toUInt32.toNat_lt
  have hyll := y.toUInt32.toNat_lt
  have hpl := (x * y).toUInt32.toNat_lt
  have hph := ((x * y) >>> 32).toUInt32.toNat_lt
  have hll : x.toUInt32.toNat * y.toUInt32.toNat / 4294967296 < 4294967296 := by
    have := Nat.mul_lt_mul_of_lt_of_lt hxll hyll
    omega
  constructor
  · apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_mul]
    omega
  · apply UInt32.toNat_inj.mp
    simp only [UInt32.toNat_add, UInt32.toNat_mul, UInt32.toNat_ofNat']
    rw [Nat.mod_eq_of_lt hll]
    omega

end Project.WGSL
