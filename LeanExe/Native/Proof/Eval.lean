import LeanExe.Native.Translate
import LeanExe.Native.Proof.Mem

/-!
The values of the operators, casts, and conditions that the translator emits, at the C types
`unsigned int` and `unsigned long long`, as Lean's fixed-width operations; and the evaluation of
the globals that hold the Wasm globals and `lx_status`.
-/

namespace LeanExe.Native

open LClight

variable (A : Archi) (m : mem)

/-! ## Operators -/

theorem sem_add_ll (x y : UInt64) :
    sem_binary_operation A .Oadd (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x + y)) := by
  rw [← Int64.add_eq]; rfl

theorem sem_sub_ll (x y : UInt64) :
    sem_binary_operation A .Osub (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x - y)) := by
  rw [← Int64.sub_eq]; rfl

theorem sem_mul_ll (x y : UInt64) :
    sem_binary_operation A .Omul (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x * y)) := by
  rw [← Int64.mul_eq]; rfl

theorem sem_and_ll (x y : UInt64) :
    sem_binary_operation A .Oand (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x &&& y)) := by
  rw [← Int64.and_eq]; rfl

theorem sem_or_ll (x y : UInt64) :
    sem_binary_operation A .Oor (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x ||| y)) := by
  rw [← Int64.or_eq]; rfl

theorem sem_xor_ll (x y : UInt64) :
    sem_binary_operation A .Oxor (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x ^^^ y)) := by
  rw [← Int64.xor_eq]; rfl

theorem sem_div_ll (x y : UInt64) (hy : y ≠ 0) :
    sem_binary_operation A .Odiv (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x / y)) := by
  rw [← Int64.divu_eq]
  have : Int64.eq y Int64.zero = false := by
    rw [Int64.eq_eq, Int64.zero_eq]; simpa using hy
  show (if Int64.eq y Int64.zero then (none : Option val) else some (val.Vlong (Int64.divu x y))) = _
  rw [this]; rfl

theorem sem_mod_ll (x y : UInt64) (hy : y ≠ 0) :
    sem_binary_operation A .Omod (.Vlong x) tulong (.Vlong y) tulong m = some (.Vlong (x % y)) := by
  rw [← Int64.modu_eq]
  have : Int64.eq y Int64.zero = false := by
    rw [Int64.eq_eq, Int64.zero_eq]; simpa using hy
  show (if Int64.eq y Int64.zero then (none : Option val) else some (val.Vlong (Int64.modu x y))) = _
  rw [this]; rfl

theorem sem_shl_ll (x y : UInt64) :
    sem_binary_operation A .Oshl (.Vlong x) tulong (.Vlong (y &&& 63)) tulong m =
      some (.Vlong (x <<< (y % 64))) := by
  rw [UInt64.and_63_eq_mod, ← Int64.shl_eq _ _ (UInt64.mod_64_lt y)]
  have : Int64.ltu (y % 64) Int64.iwordsize = true := by
    rw [Int64.ltu_eq]
    simp only [decide_eq_true_eq]
    exact UInt64.lt_iff_toNat_lt.mpr (UInt64.mod_64_lt y)
  show (if Int64.ltu (y % 64) Int64.iwordsize then some (val.Vlong (Int64.shl x (y % 64)))
    else (none : Option val)) = _
  rw [this]; rfl

theorem sem_shr_ll (x y : UInt64) :
    sem_binary_operation A .Oshr (.Vlong x) tulong (.Vlong (y &&& 63)) tulong m =
      some (.Vlong (x >>> (y % 64))) := by
  rw [UInt64.and_63_eq_mod, ← Int64.shru_eq _ _ (UInt64.mod_64_lt y)]
  have : Int64.ltu (y % 64) Int64.iwordsize = true := by
    rw [Int64.ltu_eq]
    simp only [decide_eq_true_eq]
    exact UInt64.lt_iff_toNat_lt.mpr (UInt64.mod_64_lt y)
  show (if Int64.ltu (y % 64) Int64.iwordsize then some (val.Vlong (Int64.shru x (y % 64)))
    else (none : Option val)) = _
  rw [this]; rfl

theorem sem_eq_ll (x y : UInt64) :
    sem_binary_operation A .Oeq (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vint (if x = y then 1 else 0)) := by
  show some (Val.of_bool (Int64.eq x y)) = _
  rw [Int64.eq_eq, of_bool_decide]

theorem sem_ne_ll (x y : UInt64) :
    sem_binary_operation A .One (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vint (if x ≠ y then 1 else 0)) := by
  show some (Val.of_bool (!Int64.eq x y)) = _
  rw [Int64.eq_eq, ← decide_not, of_bool_decide]

theorem sem_lt_ll (x y : UInt64) :
    sem_binary_operation A .Olt (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vint (if x < y then 1 else 0)) := by
  show some (Val.of_bool (Int64.ltu x y)) = _
  rw [Int64.ltu_eq, of_bool_decide]

theorem sem_le_ll (x y : UInt64) :
    sem_binary_operation A .Ole (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vint (if x ≤ y then 1 else 0)) := by
  show some (Val.of_bool (!Int64.ltu y x)) = _
  rw [Int64.ltu_eq, ← decide_not, of_bool_decide]
  simp only [UInt64.not_lt]

theorem sem_ge_ll (x y : UInt64) :
    sem_binary_operation A .Oge (.Vlong x) tulong (.Vlong y) tulong m =
      some (.Vint (if x ≥ y then 1 else 0)) := by
  show some (Val.of_bool (!Int64.ltu x y)) = _
  rw [Int64.ltu_eq, ← decide_not, of_bool_decide]
  simp only [UInt64.not_lt, ge_iff_le]

theorem sem_eq_ii (x y : UInt32) :
    sem_binary_operation A .Oeq (.Vint x) tuint (.Vint y) tuint m =
      some (.Vint (if x = y then 1 else 0)) := by
  show some (Val.of_bool (LClight.Int.eq x y)) = _
  rw [LClight.Int.eq_eq, of_bool_decide]

theorem sem_ne_ii (x y : UInt32) :
    sem_binary_operation A .One (.Vint x) tuint (.Vint y) tuint m =
      some (.Vint (if x ≠ y then 1 else 0)) := by
  show some (Val.of_bool (!LClight.Int.eq x y)) = _
  rw [LClight.Int.eq_eq, ← decide_not, of_bool_decide]

theorem sem_and_ii (x y : UInt32) :
    sem_binary_operation A .Oand (.Vint x) tuint (.Vint y) tuint m = some (.Vint (x &&& y)) := by
  rw [← LClight.Int.and_eq]; rfl

theorem sem_sub_ii (x y : UInt32) :
    sem_binary_operation A .Osub (.Vint x) tuint (.Vint y) tuint m =
      some (.Vint (LClight.Int.sub x y)) :=
  rfl

/-! ## Casts and conditions -/

theorem cast_int_uint (x : UInt32) : sem_cast (.Vint x) tint tuint m = some (.Vint x) := rfl

theorem cast_long_uint (x : UInt64) :
    sem_cast (.Vlong x) tulong tuint m = some (.Vint (UInt32.ofNat (x.toNat % 2 ^ 32))) := by
  show some (val.Vint (LClight.Int.repr (Int64.unsigned x))) = _
  simp only [Int64.unsigned, LClight.Int.repr_natCast]
  congr 2
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_ofNat']
  omega

theorem cast_uint_long (x : UInt32) :
    sem_cast (.Vint x) tuint tulong m = some (.Vlong (UInt64.ofNat x.toNat)) := by
  show some (val.Vlong (Int64.repr (LClight.Int.unsigned x))) = _
  simp only [LClight.Int.unsigned, Int64.repr_natCast]

theorem cast_ll (x : UInt64) : sem_cast (.Vlong x) tulong tulong m = some (.Vlong x) := rfl
theorem cast_ii (x : UInt32) : sem_cast (.Vint x) tuint tuint m = some (.Vint x) := rfl
theorem cast_dd (x : UInt64) :
    sem_cast (.Vfloat x) (VT.ty .f64) (VT.ty .f64) m = some (.Vfloat x) := rfl
theorem cast_ss (x : UInt32) :
    sem_cast (.Vsingle x) (VT.ty .f32) (VT.ty .f32) m = some (.Vsingle x) := rfl

theorem bool_uint (x : UInt32) : bool_val (.Vint x) tuint m = some (decide (x ≠ 0)) := by
  show some (!LClight.Int.eq x LClight.Int.zero) = _
  rw [LClight.Int.eq_eq, LClight.Int.zero_eq, decide_not]

theorem bool_int (x : UInt32) : bool_val (.Vint x) tint m = some (decide (x ≠ 0)) := by
  show some (!LClight.Int.eq x LClight.Int.zero) = _
  rw [LClight.Int.eq_eq, LClight.Int.zero_eq, decide_not]

end LeanExe.Native
