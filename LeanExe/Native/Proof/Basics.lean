import LeanExe.Native.Clight.Bigstep

/-!
Facts about the Lean copy of Clight that the translator's proof uses: lookups in temporary
environments, loads after stores of 4- and 8-byte integers, the integer operations of
`Integers.lean` as Lean's fixed-width operations, and the evaluation of the operators and casts
that the translator emits.
-/

namespace LClight

/-! ## Temporary environments -/

theorem te_insert_same (le : temp_env) (k : ident) (v : val) : (le.insert k v)[k]? = some v :=
  Std.TreeMap.getElem?_insert_self

theorem te_insert_ne {le : temp_env} {k a : ident} (v : val) (h : k ≠ a) :
    (le.insert k v)[a]? = le[a]? := by
  rw [Std.TreeMap.getElem?_insert]
  have : compare k a ≠ .eq := by
    intro e
    exact h (Nat.compare_eq_eq.mp e)
  simp [this]

/-! ## Integers -/

theorem Int64.repr_natCast (n : Nat) : Int64.repr (n : _root_.Int) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [Int64.repr, Int64.modulus, UInt64.toNat_ofNat']
  omega

theorem Int.repr_natCast (n : Nat) : Int.repr (n : _root_.Int) = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  simp only [Int.repr, Int.modulus, UInt32.toNat_ofNat']
  omega

theorem Int64.repr_toNat (x : UInt64) : Int64.repr (x.toNat : _root_.Int) = x := by
  rw [Int64.repr_natCast, UInt64.ofNat_toNat]

theorem Int.repr_toNat (x : UInt32) : Int.repr (x.toNat : _root_.Int) = x := by
  rw [Int.repr_natCast, UInt32.ofNat_toNat]

theorem Int64.add_eq (x y : UInt64) : Int64.add x y = x + y := by
  simp only [Int64.add, Int64.unsigned]
  rw [← Int.natCast_add, Int64.repr_natCast]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_add]

theorem Int64.sub_eq (x y : UInt64) : Int64.sub x y = x - y := by
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [Int64.sub, Int64.repr, Int64.unsigned, Int64.modulus, UInt64.toNat_ofNat',
    UInt64.toNat_sub]
  omega

theorem Int64.mul_eq (x y : UInt64) : Int64.mul x y = x * y := by
  simp only [Int64.mul, Int64.unsigned]
  rw [← Int.natCast_mul, Int64.repr_natCast]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_mul]

theorem Int64.divu_eq (x y : UInt64) : Int64.divu x y = x / y := by
  simp only [Int64.divu, Int64.unsigned]
  rw [← Int.natCast_ediv, Int64.repr_natCast]
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have : x.toNat / y.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [UInt64.toNat_ofNat', UInt64.toNat_div, Nat.mod_eq_of_lt this]

theorem Int64.modu_eq (x y : UInt64) : Int64.modu x y = x % y := by
  simp only [Int64.modu, Int64.unsigned]
  rw [← Int.natCast_emod, Int64.repr_natCast]
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have : x.toNat % y.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.mod_le _ _) hx
  simp only [UInt64.toNat_ofNat', UInt64.toNat_mod, Nat.mod_eq_of_lt this]

theorem Int64.and_eq (x y : UInt64) : Int64.and x y = x &&& y := by
  apply UInt64.toNat_inj.mp
  simp only [Int64.and, Int64.unsigned, Int.toNat_natCast, UInt64.toNat_ofNat', UInt64.toNat_and]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ y.toNat_lt)

theorem Int64.or_eq (x y : UInt64) : Int64.or x y = x ||| y := by
  apply UInt64.toNat_inj.mp
  simp only [Int64.or, Int64.unsigned, Int.toNat_natCast, UInt64.toNat_ofNat', UInt64.toNat_or]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.toNat_lt y.toNat_lt)

theorem Int64.xor_eq (x y : UInt64) : Int64.xor x y = x ^^^ y := by
  apply UInt64.toNat_inj.mp
  simp only [Int64.xor, Int64.unsigned, Int.toNat_natCast, UInt64.toNat_ofNat', UInt64.toNat_xor]
  exact Nat.mod_eq_of_lt (Nat.xor_lt_two_pow x.toNat_lt y.toNat_lt)

theorem UInt64.and_63_eq_mod (b : UInt64) : b &&& 63 = b % 64 := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, UInt64.toNat_mod]
  have : (63 : UInt64).toNat = 2 ^ 6 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]
  rfl

theorem UInt64.mod_64_lt (b : UInt64) : (b % 64).toNat < 64 := by
  rw [UInt64.toNat_mod]
  exact Nat.mod_lt _ (by decide)

theorem Int64.shl_eq (x k : UInt64) (hk : k.toNat < 64) : Int64.shl x k = x <<< k := by
  unfold Int64.shl
  rw [ite_eq_left (by simp only [Int64.unsigned]; omega)]
  simp only [Int64.unsigned, Int.toNat_natCast]
  have e : (x.toNat : _root_.Int) * 2 ^ k.toNat = ((x.toNat * 2 ^ k.toNat : Nat) : _root_.Int) := by
    norm_cast
  rw [e, Int64.repr_natCast]
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_ofNat', UInt64.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]

theorem Int64.shru_eq (x k : UInt64) (hk : k.toNat < 64) : Int64.shru x k = x >>> k := by
  unfold Int64.shru
  rw [ite_eq_left (by simp only [Int64.unsigned]; omega)]
  simp only [Int64.unsigned, Int.toNat_natCast]
  have e : (x.toNat : _root_.Int) / 2 ^ k.toNat = ((x.toNat / 2 ^ k.toNat : Nat) : _root_.Int) := by
    norm_cast
  rw [e, Int64.repr_natCast]
  apply UInt64.toNat_inj.mp
  have hx := x.toNat_lt
  have : x.toNat / 2 ^ k.toNat < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [UInt64.toNat_ofNat', UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt this]

theorem Int64.eq_eq (x y : UInt64) : Int64.eq x y = decide (x = y) := by
  simp only [Int64.eq, Int64.unsigned, Int.ofNat_inj, decide_eq_decide]
  exact UInt64.toNat_inj

theorem Int64.ltu_eq (x y : UInt64) : Int64.ltu x y = decide (x < y) := by
  simp only [Int64.ltu, Int64.unsigned, Int.ofNat_lt, decide_eq_decide]
  exact UInt64.lt_iff_toNat_lt.symm

theorem Int.eq_eq (x y : UInt32) : Int.eq x y = decide (x = y) := by
  simp only [Int.eq, Int.unsigned, Int.ofNat_inj, decide_eq_decide]
  exact UInt32.toNat_inj

theorem Int.and_eq (x y : UInt32) : Int.and x y = x &&& y := by
  apply UInt32.toNat_inj.mp
  simp only [Int.and, Int.unsigned, Int.toNat_natCast, UInt32.toNat_ofNat', UInt32.toNat_and]
  exact Nat.mod_eq_of_lt (Nat.and_lt_two_pow _ y.toNat_lt)

theorem Int.add_eq (x y : UInt32) : Int.add x y = x + y := by
  simp only [Int.add, Int.unsigned]
  rw [← Int.natCast_add, Int.repr_natCast]
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_add]

theorem Int.sub_eq (x y : UInt32) : Int.sub x y = x - y := by
  apply UInt32.toNat_inj.mp
  have hx := x.toNat_lt
  have hy := y.toNat_lt
  simp only [Int.sub, Int.repr, Int.unsigned, Int.modulus, UInt32.toNat_ofNat',
    UInt32.toNat_sub]
  omega

theorem Int.or_eq (x y : UInt32) : Int.or x y = x ||| y := by
  apply UInt32.toNat_inj.mp
  simp only [Int.or, Int.unsigned, Int.toNat_natCast, UInt32.toNat_ofNat', UInt32.toNat_or]
  exact Nat.mod_eq_of_lt (Nat.or_lt_two_pow x.toNat_lt y.toNat_lt)

theorem Int.shl_eq (x k : UInt32) (hk : k.toNat < 32) : Int.shl x k = x <<< k := by
  unfold Int.shl
  rw [ite_eq_left (by simp only [Int.unsigned]; omega)]
  simp only [Int.unsigned, Int.toNat_natCast]
  have e : (x.toNat : _root_.Int) * 2 ^ k.toNat = ((x.toNat * 2 ^ k.toNat : Nat) : _root_.Int) := by
    norm_cast
  rw [e, Int.repr_natCast]
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat', UInt32.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt hk]

theorem Int.shru_eq (x k : UInt32) (hk : k.toNat < 32) : Int.shru x k = x >>> k := by
  unfold Int.shru
  rw [ite_eq_left (by simp only [Int.unsigned]; omega)]
  simp only [Int.unsigned, Int.toNat_natCast]
  have e : (x.toNat : _root_.Int) / 2 ^ k.toNat = ((x.toNat / 2 ^ k.toNat : Nat) : _root_.Int) := by
    norm_cast
  rw [e, Int.repr_natCast]
  apply UInt32.toNat_inj.mp
  have hx := x.toNat_lt
  have : x.toNat / 2 ^ k.toNat < 2 ^ 32 := Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hx
  simp only [UInt32.toNat_ofNat', UInt32.toNat_shiftRight, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt this]

theorem Int.ltu_eq (x y : UInt32) : Int.ltu x y = decide (x < y) := by
  simp only [Int.ltu, Int.unsigned, Int.ofNat_lt, decide_eq_decide]
  exact UInt32.lt_iff_toNat_lt.symm

theorem Int.sub_one_eq (k : Nat) (_hk : k + 1 < 2 ^ 32) :
    Int.sub (UInt32.ofNat (k + 1)) (UInt32.ofNat 1) = UInt32.ofNat k := by
  apply UInt32.toNat_inj.mp
  simp only [Int.sub, Int.repr, Int.unsigned, Int.modulus, UInt32.toNat_ofNat']
  omega

theorem Int64.zero_eq : Int64.zero = 0 := rfl
theorem Int.zero_eq : Int.zero = 0 := rfl
theorem Int.one_eq : Int.one = 1 := rfl

/-! ## Values of comparisons -/

theorem of_bool_true : Val.of_bool true = .Vint 1 := rfl
theorem of_bool_false : Val.of_bool false = .Vint 0 := rfl

theorem of_bool_decide (p : Prop) [Decidable p] :
    Val.of_bool (decide p) = .Vint (if p then 1 else 0) := by
  by_cases h : p <;> simp [h, Val.of_bool, Vtrue, Vfalse, Int.one, Int.zero, Int.repr, Int.modulus]

end LClight
