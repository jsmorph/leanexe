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

/-- The difference of the pairs in variables `a` and `b`, with the borrow of the low halves. -/
def sub64 (a b : Nat) : Expr :=
  .vec2 (.bin .sub (.fst a) (.fst b))
    (.bin .sub (.bin .sub (.snd a) (.snd b)) (.select (.lit 0) (.lit 1) (.bin .lt (.fst a) (.fst b))))

/-- Whether the pairs in variables `a` and `b` are equal. -/
def eq64 (a b : Nat) : Expr :=
  .bin .and (.bin .eq (.fst a) (.fst b)) (.bin .eq (.snd a) (.snd b))

/-- Whether the pair in variable `a` is at most the pair in `b`. -/
def le64 (a b : Nat) : Expr :=
  .bin .or (.bin .lt (.snd a) (.snd b))
    (.bin .and (.bin .eq (.snd a) (.snd b)) (.bin .le (.fst a) (.fst b)))

/-- The quotient of the pair in variable `a` by `2^s`, for `1 ≤ s ≤ 31`: the high half's
remainder moves into the low half. -/
def divPow2 (a s : Nat) : Expr :=
  let c := Expr.lit (UInt32.ofNat (2 ^ s))
  .vec2 (.bin .add (.bin .div (.fst a) c)
      (.bin .mul (.bin .sub (.snd a) (.bin .mul (.bin .div (.snd a) c) c))
        (.lit (UInt32.ofNat (2 ^ (32 - s))))))
    (.bin .div (.snd a) c)

/-- The remainder of the pair in variable `a` modulo `2^s`, for `1 ≤ s ≤ 31`. -/
def remPow2 (a s : Nat) : Expr :=
  let c := Expr.lit (UInt32.ofNat (2 ^ s))
  .vec2 (.bin .sub (.fst a) (.bin .mul (.bin .div (.fst a) c) c)) (.lit 0)

theorem sub64_word (ctx : Context) (env : Env) {ma mb : Bool} (a b : Nat) (x y : UInt64)
    (ha : env.find a = some (pairOf x, ma)) (hb : env.find b = some (pairOf y, mb)) :
    (sub64 a b).eval ctx env = some (pairOf (x - y)) := by
  have hx := toNat_of_halves x
  have hy := toNat_of_halves y
  have hs := toNat_of_halves (x - y)
  have hxl := x.toUInt32.toNat_lt
  have hyl := y.toUInt32.toNat_lt
  have hxh := (x >>> 32).toUInt32.toNat_lt
  have hyh := (y >>> 32).toUInt32.toNat_lt
  have hsl := (x - y).toUInt32.toNat_lt
  have hsh := ((x - y) >>> 32).toUInt32.toNat_lt
  have hdiff : (x - y).toNat = (2 ^ 64 - y.toNat + x.toNat) % 2 ^ 64 := UInt64.toNat_sub x y
  have hyn := y.toNat_lt
  simp only [pairOf] at ha hb ⊢
  by_cases h : x.toUInt32.toNat < y.toUInt32.toNat
  · have hlt : x.toUInt32 < y.toUInt32 := by simpa [UInt32.lt_iff_toNat_lt] using h
    simp [sub64, Expr.eval, ha, hb, BinOp.apply, hlt, Value.sameType]
    all_goals first
      | (apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_sub, UInt32.toNat_ofNat',
          UInt32.reduceToNat]; omega)
      | (constructor <;> apply UInt32.toNat_inj.mp <;>
          simp only [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.reduceToNat] <;> omega)
  · have hlt : ¬ x.toUInt32 < y.toUInt32 := by simpa [UInt32.lt_iff_toNat_lt] using h
    simp [sub64, Expr.eval, ha, hb, BinOp.apply, hlt, Value.sameType]
    all_goals first
      | (apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_sub, UInt32.toNat_ofNat',
          UInt32.reduceToNat]; omega)
      | (constructor <;> apply UInt32.toNat_inj.mp <;>
          simp only [UInt32.toNat_sub, UInt32.toNat_ofNat', UInt32.reduceToNat] <;> omega)

theorem eq64_word (ctx : Context) (env : Env) {ma mb : Bool} (a b : Nat) (x y : UInt64)
    (ha : env.find a = some (pairOf x, ma)) (hb : env.find b = some (pairOf y, mb)) :
    (eq64 a b).eval ctx env = some (.bool (x == y)) := by
  have hx := toNat_of_halves x
  have hy := toNat_of_halves y
  have hxl := x.toUInt32.toNat_lt
  have hyl := y.toUInt32.toNat_lt
  have key : (x == y) = ((x.toUInt32 == y.toUInt32) && ((x >>> 32).toUInt32 == (y >>> 32).toUInt32)) := by
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, Bool.and_eq_true]
    constructor
    · rintro rfl; exact ⟨rfl, rfl⟩
    · rintro ⟨h1, h2⟩
      apply UInt64.toNat_inj.mp
      have := congrArg UInt32.toNat h1
      have := congrArg UInt32.toNat h2
      omega
  rw [key]
  simp only [pairOf] at ha hb
  generalize (x >>> 32).toUInt32 = xh at ha ⊢
  generalize x.toUInt32 = xl at ha ⊢
  generalize (y >>> 32).toUInt32 = yh at hb ⊢
  generalize y.toUInt32 = yl at hb ⊢
  cases h1 : (xl == yl) <;> cases h2 : (xh == yh) <;>
    simp [eq64, Expr.eval, ha, hb, BinOp.apply, h1, h2]

theorem le64_word (ctx : Context) (env : Env) {ma mb : Bool} (a b : Nat) (x y : UInt64)
    (ha : env.find a = some (pairOf x, ma)) (hb : env.find b = some (pairOf y, mb)) :
    (le64 a b).eval ctx env = some (.bool (decide (x ≤ y))) := by
  have hx := toNat_of_halves x
  have hy := toNat_of_halves y
  have hxl := x.toUInt32.toNat_lt
  have hyl := y.toUInt32.toNat_lt
  have key : decide (x ≤ y) = (decide ((x >>> 32).toUInt32 < (y >>> 32).toUInt32) ||
      (((x >>> 32).toUInt32 == (y >>> 32).toUInt32) && decide (x.toUInt32 ≤ y.toUInt32))) := by
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      UInt64.le_iff_toNat_le, UInt32.lt_iff_toNat_lt, UInt32.le_iff_toNat_le]
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
  cases h1 : decide (xh < yh) <;> cases h2 : (xh == yh) <;> cases h3 : decide (xl ≤ yl) <;>
    simp [le64, Expr.eval, ha, hb, BinOp.apply, h1, h2, h3]

theorem u32_sub_div_mul (x c : UInt32) (hc : 0 < c.toNat) :
    (x - x / c * c).toNat = x.toNat % c.toNat := by
  have hx := x.toNat_lt
  have h1 : (x / c * c).toNat = x.toNat / c.toNat * c.toNat := by
    rw [UInt32.toNat_mul, UInt32.toNat_div]
    apply Nat.mod_eq_of_lt
    have := Nat.div_mul_le_self x.toNat c.toNat
    omega
  have hle : x / c * c ≤ x := by
    rw [UInt32.le_iff_toNat_le, h1]; exact Nat.div_mul_le_self _ _
  rw [UInt32.toNat_sub_of_le _ _ hle, h1]
  have := Nat.div_add_mod' x.toNat c.toNat
  generalize x.toNat / c.toNat * c.toNat = T at *
  omega

theorem divPow2_nat (xh xl s : Nat) (hs : 1 ≤ s ∧ s ≤ 31) (hxl : xl < 2 ^ 32) :
    (xh * 2 ^ 32 + xl) / 2 ^ s % 2 ^ 32 = xl / 2 ^ s + (xh % 2 ^ s) * 2 ^ (32 - s) ∧
    (xh * 2 ^ 32 + xl) / 2 ^ s / 2 ^ 32 = xh / 2 ^ s := by
  obtain ⟨h1, h2⟩ := hs
  interval_cases s <;> omega

theorem divPow2_word (ctx : Context) (env : Env) {ma : Bool} (a s : Nat) (x : UInt64)
    (hs : 1 ≤ s ∧ s ≤ 31) (ha : env.find a = some (pairOf x, ma)) :
    (divPow2 a s).eval ctx env = some (pairOf (x / UInt64.ofNat (2 ^ s))) := by
  have hx := toNat_of_halves x
  have hxl := x.toUInt32.toNat_lt
  have hxh := (x >>> 32).toUInt32.toNat_lt
  have hq := toNat_of_halves (x / UInt64.ofNat (2 ^ s))
  have hpow : (2 : Nat) ^ s < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpow' : (2 : Nat) ^ (32 - s) < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpos : 0 < (2 : Nat) ^ s := Nat.two_pow_pos s
  have hc64 : (UInt64.ofNat (2 ^ s)).toNat = 2 ^ s := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hc32 : (UInt32.ofNat (2 ^ s)).toNat = 2 ^ s := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hpow
  have hd32 : (UInt32.ofNat (2 ^ (32 - s))).toNat = 2 ^ (32 - s) := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hpow'
  have hne : UInt32.ofNat (2 ^ s) ≠ 0 := fun h => by
    have := congrArg UInt32.toNat h; rw [hc32] at this; simp at this
  have hqn : (x / UInt64.ofNat (2 ^ s)).toNat = x.toNat / 2 ^ s := by
    rw [UInt64.toNat_div, hc64]
  obtain ⟨key1, key2⟩ := divPow2_nat (x >>> 32).toUInt32.toNat x.toUInt32.toNat s hs hxl
  rw [show (x >>> 32).toUInt32.toNat * 2 ^ 32 + x.toUInt32.toNat = x.toNat by omega] at key1 key2
  simp only [pairOf] at ha ⊢
  simp only [divPow2, Expr.eval, ha, BinOp.apply, hne, ↓reduceIte, Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq, Value.vec2.injEq]
  have hlow := (x / UInt64.ofNat (2 ^ s)).toUInt32.toNat_lt
  have hhigh := ((x / UInt64.ofNat (2 ^ s)) >>> 32).toUInt32.toNat_lt
  have hmodlt : (x >>> 32).toUInt32.toNat % 2 ^ s * 2 ^ (32 - s) < 2 ^ 32 := by
    have := Nat.mod_lt (x >>> 32).toUInt32.toNat hpos
    calc (x >>> 32).toUInt32.toNat % 2 ^ s * 2 ^ (32 - s) < 2 ^ s * 2 ^ (32 - s) :=
          Nat.mul_lt_mul_of_pos_right this (Nat.two_pow_pos _)
      _ = 2 ^ 32 := by rw [← Nat.pow_add]; congr 1; omega
  have hc0 : 0 < (UInt32.ofNat (2 ^ s)).toNat := by rw [hc32]; exact hpos
  constructor
  · apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_mul, u32_sub_div_mul _ _ hc0, UInt32.toNat_div, hc32, hd32,
      Nat.mod_eq_of_lt hmodlt, UInt64.toNat_toUInt32 (x / UInt64.ofNat (2 ^ s)), hqn, key1]
    apply Nat.mod_eq_of_lt
    rw [← key1]
    exact Nat.mod_lt _ (by decide)
  · apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_div, hc32, ← key2,
      UInt64.toNat_toUInt32 ((x / UInt64.ofNat (2 ^ s)) >>> 32), UInt64.toNat_shiftRight, hqn]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow]
    have : x.toNat / 2 ^ s / 2 ^ 32 < 2 ^ 32 := by
      have := x.toNat_lt
      have := Nat.div_le_self x.toNat (2 ^ s)
      omega
    exact (Nat.mod_eq_of_lt this).symm

theorem remPow2_word (ctx : Context) (env : Env) {ma : Bool} (a s : Nat) (x : UInt64)
    (hs : 1 ≤ s ∧ s ≤ 31) (ha : env.find a = some (pairOf x, ma)) :
    (remPow2 a s).eval ctx env = some (pairOf (x % UInt64.ofNat (2 ^ s))) := by
  have hx := toNat_of_halves x
  have hxl := x.toUInt32.toNat_lt
  have hr := toNat_of_halves (x % UInt64.ofNat (2 ^ s))
  have hpow : (2 : Nat) ^ s < 2 ^ 32 := Nat.pow_lt_pow_right (by omega) (by omega)
  have hpos : 0 < (2 : Nat) ^ s := Nat.two_pow_pos s
  have hc64 : (UInt64.ofNat (2 ^ s)).toNat = 2 ^ s := by
    rw [UInt64.toNat_ofNat']; exact Nat.mod_eq_of_lt (by omega)
  have hc32 : (UInt32.ofNat (2 ^ s)).toNat = 2 ^ s := by
    rw [UInt32.toNat_ofNat']; exact Nat.mod_eq_of_lt hpow
  have hne : UInt32.ofNat (2 ^ s) ≠ 0 := fun h => by
    have := congrArg UInt32.toNat h; rw [hc32] at this; simp at this
  have hrn : (x % UInt64.ofNat (2 ^ s)).toNat = x.toNat % 2 ^ s := by
    rw [UInt64.toNat_mod, hc64]
  have hmod32 : x.toNat % 2 ^ s = x.toUInt32.toNat % 2 ^ s := by
    obtain ⟨h1, h2⟩ := hs
    rw [hx]
    interval_cases s <;> omega
  have hrlt : x.toNat % 2 ^ s < 2 ^ s := Nat.mod_lt _ hpos
  have hc0 : 0 < (UInt32.ofNat (2 ^ s)).toNat := by rw [hc32]; exact hpos
  simp only [pairOf] at ha ⊢
  simp only [remPow2, Expr.eval, ha, BinOp.apply, hne, ↓reduceIte, Option.bind_eq_bind,
    Option.bind_some, Option.some.injEq, Value.vec2.injEq]
  constructor
  · apply UInt32.toNat_inj.mp
    rw [u32_sub_div_mul _ _ hc0, hc32, UInt64.toNat_toUInt32 (x % UInt64.ofNat (2 ^ s)), hrn,
      hmod32]
    rw [hmod32] at hrlt
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · apply UInt32.toNat_inj.mp
    rw [UInt64.toNat_toUInt32 ((x % UInt64.ofNat (2 ^ s)) >>> 32), UInt64.toNat_shiftRight, hrn]
    simp only [UInt64.reduceToNat, Nat.reduceMod, Nat.shiftRight_eq_div_pow, UInt32.toNat_zero]
    have : x.toNat % 2 ^ s / 2 ^ 32 = 0 := Nat.div_eq_of_lt (by omega)
    rw [this]

end Project.WGSL
