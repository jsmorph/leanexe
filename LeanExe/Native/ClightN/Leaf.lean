import LeanExe.Native.ClightN.Laws

/-!
The leaf forms of `clightn/N.nsx`, proved of the Lean copy of Clight at `Archi.aarch64`: for each
operator, cast, and truth value at the types that the translator emits, the copy's result is
exactly what the leaf relation gives, and a constant evaluates to its value.  Each proof first
computes the copy's definition on every shape of value (the lemmas `eq_*`, proved by `rfl` after
case analysis), then relates the result to the relation's rules.  Rocq proves the same statements
of CompCert 3.18 in `clightn/rocq/NProof.v`.
-/

namespace ClightN.Proof

open LClight ClightN.Base ClightN.Spec

abbrev tul : type := .Tlong .Unsigned (attr.mk false none)
abbrev tsl : type := .Tlong .Signed (attr.mk false none)
abbrev tui : type := .Tint .I32 .Unsigned (attr.mk false none)
abbrev tsi : type := .Tint .I32 .Signed (attr.mk false none)
abbrev tuc : type := .Tint .I8 .Unsigned (attr.mk false none)
abbrev tvui : type := .Tint .I32 .Unsigned (attr.mk true none)
abbrev tvuc : type := .Tint .I8 .Unsigned (attr.mk true none)

/-! ## Shapes of values -/

/-- `f` of two words of 64 bits, and nothing for other values. -/
def onLongs (f : UInt64 → UInt64 → Option val) : val → val → Option val
  | .Vlong x, .Vlong y => f x y
  | _, _ => none

/-- `f` of two words of 32 bits, and nothing for other values. -/
def onInts (f : UInt32 → UInt32 → Option val) : val → val → Option val
  | .Vint x, .Vint y => f x y
  | _, _ => none

/-- `f` of a word of 64 bits, and nothing for other values. -/
def onLong (f : UInt64 → Option val) : val → Option val
  | .Vlong x => f x
  | _ => none

/-- `f` of a word of 32 bits, and nothing for other values. -/
def onInt {α : Type} (f : UInt32 → Option α) : val → Option α
  | .Vint x => f x
  | _ => none

/-- A word of 64 bits or a pointer, unchanged, and nothing for other values. -/
def passLong : val → Option val
  | .Vlong x => some (.Vlong x)
  | .Vptr b o => some (.Vptr b o)
  | _ => none

theorem onLongs_some {f : UInt64 → UInt64 → Option val} {v1 v2 v : val} :
    onLongs f v1 v2 = some v ↔ ∃ x y, v1 = .Vlong x ∧ v2 = .Vlong y ∧ f x y = some v := by
  cases v1 <;> cases v2 <;> simp [onLongs]

theorem onInts_some {f : UInt32 → UInt32 → Option val} {v1 v2 v : val} :
    onInts f v1 v2 = some v ↔ ∃ x y, v1 = .Vint x ∧ v2 = .Vint y ∧ f x y = some v := by
  cases v1 <;> cases v2 <;> simp [onInts]

theorem onLong_some {f : UInt64 → Option val} {v1 v : val} :
    onLong f v1 = some v ↔ ∃ x, v1 = .Vlong x ∧ f x = some v := by
  cases v1 <;> simp [onLong]

theorem onInt_some {α : Type} {f : UInt32 → Option α} {v1 : val} {v : α} :
    onInt f v1 = some v ↔ ∃ x, v1 = .Vint x ∧ f x = some v := by
  cases v1 <;> simp [onInt]

/-! ## Words -/

theorem long_eq_zero (y : UInt64) :
    LClight.Int64.eq y LClight.Int64.zero = true ↔ u64 y = 0 := by
  show decide (u64 y = LClight.Int64.unsigned LClight.Int64.zero) = true ↔ _
  rw [decide_eq_true_iff]
  exact Iff.rfl

theorem long_ltu_64 (y : UInt64) :
    LClight.Int64.ltu y LClight.Int64.iwordsize = true ↔ u64 y < 64 := by
  show decide (u64 y < LClight.Int64.unsigned LClight.Int64.iwordsize) = true ↔ _
  rw [decide_eq_true_iff]
  exact Iff.rfl

theorem int_ltu_32 (y : UInt32) :
    LClight.Int.ltu y LClight.Int.iwordsize = true ↔ u32 y < 32 := by
  show decide (u32 y < LClight.Int.unsigned LClight.Int.iwordsize) = true ↔ _
  rw [decide_eq_true_iff]
  exact Iff.rfl

theorem int_eq_zero (y : UInt32) : LClight.Int.eq y LClight.Int.zero = true ↔ u32 y = 0 := by
  show decide (u32 y = LClight.Int.unsigned LClight.Int.zero) = true ↔ _
  rw [decide_eq_true_iff]
  exact Iff.rfl

theorem long_shl (x y : UInt64) (h : u64 y < 64) :
    LClight.Int64.shl x y = r64 (u64 x * pow2 (u64 y)) := by
  show (if u64 y < 64 then _ else _) = _
  rw [ite_eq_left h]
  rfl

theorem long_shru (x y : UInt64) (h : u64 y < 64) :
    LClight.Int64.shru x y = r64 (zdiv (u64 x) (pow2 (u64 y))) := by
  show (if u64 y < 64 then _ else _) = _
  rw [ite_eq_left h]
  rfl

theorem long_shr (x y : UInt64) (h : u64 y < 64) :
    LClight.Int64.shr x y = r64 (zdiv (s64 x) (pow2 (u64 y))) := by
  show (if u64 y < 64 then _ else _) = _
  rw [ite_eq_left h]
  rfl

theorem int_shl (x y : UInt32) (h : u32 y < 32) :
    LClight.Int.shl x y = r32 (u32 x * pow2 (u32 y)) := by
  show (if u32 y < 32 then _ else _) = _
  rw [ite_eq_left h]
  rfl

theorem int_shru (x y : UInt32) (h : u32 y < 32) :
    LClight.Int.shru x y = r32 (zdiv (u32 x) (pow2 (u32 y))) := by
  show (if u32 y < 32 then _ else _) = _
  rw [ite_eq_left h]
  rfl

theorem repr64_nat (n : Nat) : r64 (n : _root_.Int) = UInt64.ofNat n := by
  apply UInt64.toNat_inj.mp
  simp only [r64, LClight.Int64.repr, modulus64, UInt64.toNat_ofNat', Nat.reducePow]
  omega

theorem repr32_nat (n : Nat) : r32 (n : _root_.Int) = UInt32.ofNat n := by
  apply UInt32.toNat_inj.mp
  simp only [r32, LClight.Int.repr, modulus32, UInt32.toNat_ofNat', Nat.reducePow]
  omega

theorem long_and (x y : UInt64) : LClight.Int64.and x y = r64 (land (u64 x) (u64 y)) :=
  (repr64_nat _).symm

theorem long_or (x y : UInt64) : LClight.Int64.or x y = r64 (lor (u64 x) (u64 y)) :=
  (repr64_nat _).symm

theorem long_xor (x y : UInt64) : LClight.Int64.xor x y = r64 (lxor (u64 x) (u64 y)) :=
  (repr64_nat _).symm

theorem int_and (x y : UInt32) : LClight.Int.and x y = r32 (land (u32 x) (u32 y)) :=
  (repr32_nat _).symm

theorem zero_ext8 (x : UInt32) : LClight.Int.zero_ext 8 x = r32 (zmod (u32 x) 256) := rfl

theorem zero_ext8_long (x : UInt64) :
    LClight.Int.zero_ext 8 (LClight.Int.repr (LClight.Int64.unsigned x)) =
      r32 (zmod (u64 x) 256) := by
  rw [zero_ext8]
  have h : u32 (r32 (u64 x)) = zmod (u64 x) 4294967296 := u32_r32 (u64 x)
  show r32 (zmod (u32 (r32 (u64 x))) 256) = _
  rw [h]
  simp only [zmod]
  congr 1
  omega

/-! ## Comparisons -/

/-- The comparison `c` of two numbers. -/
def holds : comparison → _root_.Int → _root_.Int → Prop
  | .Ceq, a, b => a = b
  | .Cne, a, b => ¬ a = b
  | .Clt, a, b => a < b
  | .Cle, a, b => a ≤ b
  | .Cgt, a, b => b < a
  | .Cge, a, b => b ≤ a

theorem cmpu_long (c : comparison) (x y : UInt64) :
    LClight.Int64.cmpu c x y = true ↔ holds c (u64 x) (u64 y) := by
  cases c
  · show decide (u64 x = u64 y) = true ↔ _
    simp [holds]
  · show (!decide (u64 x = u64 y)) = true ↔ _
    simp [holds]
  · show decide (u64 x < u64 y) = true ↔ _
    simp [holds]
  · show (!decide (u64 y < u64 x)) = true ↔ _
    simp [holds]
  · show decide (u64 y < u64 x) = true ↔ _
    simp [holds]
  · show (!decide (u64 x < u64 y)) = true ↔ _
    simp [holds]

theorem cmpu_int (c : comparison) (x y : UInt32) :
    LClight.Int.cmpu c x y = true ↔ holds c (u32 x) (u32 y) := by
  cases c
  · show decide (u32 x = u32 y) = true ↔ _
    simp [holds]
  · show (!decide (u32 x = u32 y)) = true ↔ _
    simp [holds]
  · show decide (u32 x < u32 y) = true ↔ _
    simp [holds]
  · show (!decide (u32 y < u32 x)) = true ↔ _
    simp [holds]
  · show decide (u32 y < u32 x) = true ↔ _
    simp [holds]
  · show (!decide (u32 x < u32 y)) = true ↔ _
    simp [holds]

theorem cmp_long_lt (x y : UInt64) :
    LClight.Int64.cmp .Clt x y = true ↔ holds .Clt (s64 x) (s64 y) := by
  show decide (s64 x < s64 y) = true ↔ _
  simp [holds]

theorem cmp_long_le (x y : UInt64) :
    LClight.Int64.cmp .Cle x y = true ↔ holds .Cle (s64 x) (s64 y) := by
  show (!decide (s64 y < s64 x)) = true ↔ _
  simp [holds]

theorem of_bool_cases {b : Bool} {p : Prop} (hc : b = true ↔ p) :
    (p ∧ Val.of_bool b = .Vint (r32 1)) ∨ (¬ p ∧ Val.of_bool b = .Vint (r32 0)) := by
  cases b
  · exact .inr ⟨fun h => Bool.false_ne_true (hc.2 h), rfl⟩
  · exact .inl ⟨hc.1 rfl, rfl⟩

theorem of_bool_one {b : Bool} {p : Prop} (hc : b = true ↔ p) (h : p) :
    Val.of_bool b = .Vint (r32 1) := by
  rw [hc.2 h]
  rfl

theorem of_bool_zero {b : Bool} {p : Prop} (hc : b = true ↔ p) (h : ¬ p) :
    Val.of_bool b = .Vint (r32 0) := by
  cases b
  · rfl
  · exact absurd (hc.1 rfl) h

/-! ## Operators on unsigned long -/

theorem eq_add_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oadd v1 tul v2 tul m = onLongs (fun x y =>
      some (.Vlong (r64 (u64 x + u64 y)))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem add_ul_ul : stmt_add_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_add_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .bo_add_ul x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

theorem eq_sub_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Osub v1 tul v2 tul m = onLongs (fun x y =>
      some (.Vlong (r64 (u64 x - u64 y)))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem sub_ul_ul : stmt_sub_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_sub_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .bo_sub_ul x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

theorem eq_mul_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Omul v1 tul v2 tul m = onLongs (fun x y =>
      some (.Vlong (r64 (u64 x * u64 y)))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem mul_ul_ul : stmt_mul_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_mul_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .bo_mul_ul x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

theorem eq_div_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Odiv v1 tul v2 tul m = onLongs (fun x y =>
      if LClight.Int64.eq y LClight.Int64.zero then none
      else some (.Vlong (r64 (zdiv (u64 x) (u64 y))))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem div_ul_ul : stmt_div_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_div_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · cases h
    · rename_i hy
      obtain rfl := Option.some.inj h
      exact .bo_div_ul x y fun e => hy ((long_eq_zero y).2 e)
  · intro h
    cases h with
    | bo_div_ul x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_right fun e => hy ((long_eq_zero y).1 e)]

theorem eq_mod_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Omod v1 tul v2 tul m = onLongs (fun x y =>
      if LClight.Int64.eq y LClight.Int64.zero then none
      else some (.Vlong (r64 (zmod (u64 x) (u64 y))))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem mod_ul_ul : stmt_mod_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_mod_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · cases h
    · rename_i hy
      obtain rfl := Option.some.inj h
      exact .bo_mod_ul x y fun e => hy ((long_eq_zero y).2 e)
  · intro h
    cases h with
    | bo_mod_ul x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_right fun e => hy ((long_eq_zero y).1 e)]

theorem eq_and_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oand v1 tul v2 tul m = onLongs (fun x y =>
      some (.Vlong (LClight.Int64.and x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem and_ul_ul : stmt_and_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_and_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rw [long_and]
    exact .bo_and_ul x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, by rw [long_and]⟩

theorem eq_or_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oor v1 tul v2 tul m = onLongs (fun x y =>
      some (.Vlong (LClight.Int64.or x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem or_ul_ul : stmt_or_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_or_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rw [long_or]
    exact .bo_or_ul x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, by rw [long_or]⟩

theorem eq_xor_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oxor v1 tul v2 tul m = onLongs (fun x y =>
      some (.Vlong (LClight.Int64.xor x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem xor_ul_ul : stmt_xor_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_xor_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rw [long_xor]
    exact .bo_xor_ul x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, by rw [long_xor]⟩

theorem eq_shl_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oshl v1 tul v2 tul m = onLongs (fun x y =>
      if LClight.Int64.ltu y LClight.Int64.iwordsize then some (.Vlong (LClight.Int64.shl x y))
      else none) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem shl_ul_ul : stmt_shl_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_shl_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · rename_i hy
      obtain rfl := Option.some.inj h
      have hy' := (long_ltu_64 y).1 hy
      rw [long_shl x y hy']
      exact .bo_shl_ul x y hy'
    · cases h
  · intro h
    cases h with
    | bo_shl_ul x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_left ((long_ltu_64 y).2 hy), long_shl x y hy]

theorem eq_shr_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oshr v1 tul v2 tul m = onLongs (fun x y =>
      if LClight.Int64.ltu y LClight.Int64.iwordsize then some (.Vlong (LClight.Int64.shru x y))
      else none) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem shr_ul_ul : stmt_shr_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_shr_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · rename_i hy
      obtain rfl := Option.some.inj h
      have hy' := (long_ltu_64 y).1 hy
      rw [long_shru x y hy']
      exact .bo_shr_ul x y hy'
    · cases h
  · intro h
    cases h with
    | bo_shr_ul x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_left ((long_ltu_64 y).2 hy), long_shru x y hy]

theorem eq_eq_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oeq v1 tul v2 tul m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmpu .Ceq x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem eq_ul_ul : stmt_eq_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_eq_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_long .Ceq x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_eq_ul_1 x y (by omega)
    · exact .bo_eq_ul_0 x y (by omega)
  · intro h
    cases h with
    | bo_eq_ul_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_long .Ceq x y) (by simp only [holds]; omega)]
    | bo_eq_ul_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_long .Ceq x y) (by simp only [holds]; omega)]

theorem eq_ne_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .One v1 tul v2 tul m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmpu .Cne x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem ne_ul_ul : stmt_ne_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_ne_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_long .Cne x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_ne_ul_1 x y (by omega)
    · exact .bo_ne_ul_0 x y (by omega)
  · intro h
    cases h with
    | bo_ne_ul_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_long .Cne x y) (by simp only [holds]; omega)]
    | bo_ne_ul_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_long .Cne x y) (by simp only [holds]; omega)]

theorem eq_lt_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Olt v1 tul v2 tul m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmpu .Clt x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem lt_ul_ul : stmt_lt_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_lt_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_long .Clt x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_lt_ul_1 x y (by omega)
    · exact .bo_lt_ul_0 x y (by omega)
  · intro h
    cases h with
    | bo_lt_ul_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_long .Clt x y) (by simp only [holds]; omega)]
    | bo_lt_ul_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_long .Clt x y) (by simp only [holds]; omega)]

theorem eq_le_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Ole v1 tul v2 tul m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmpu .Cle x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem le_ul_ul : stmt_le_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_le_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_long .Cle x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_le_ul_1 x y (by omega)
    · exact .bo_le_ul_0 x y (by omega)
  · intro h
    cases h with
    | bo_le_ul_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_long .Cle x y) (by simp only [holds]; omega)]
    | bo_le_ul_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_long .Cle x y) (by simp only [holds]; omega)]

theorem eq_gt_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Ogt v1 tul v2 tul m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmpu .Cgt x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem gt_ul_ul : stmt_gt_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_gt_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_long .Cgt x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_gt_ul_1 x y (by omega)
    · exact .bo_gt_ul_0 x y (by omega)
  · intro h
    cases h with
    | bo_gt_ul_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_long .Cgt x y) (by simp only [holds]; omega)]
    | bo_gt_ul_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_long .Cgt x y) (by simp only [holds]; omega)]

theorem eq_ge_ul_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oge v1 tul v2 tul m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmpu .Cge x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem ge_ul_ul : stmt_ge_ul_ul := by
  intro ce v1 v2 v m
  rw [eq_ge_ul_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_long .Cge x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_ge_ul_1 x y (by omega)
    · exact .bo_ge_ul_0 x y (by omega)
  · intro h
    cases h with
    | bo_ge_ul_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_long .Cge x y) (by simp only [holds]; omega)]
    | bo_ge_ul_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_long .Cge x y) (by simp only [holds]; omega)]

/-! ## Operators on long -/

theorem eq_lt_sl_sl (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Olt v1 tsl v2 tsl m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmp .Clt x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem lt_sl_sl : stmt_lt_sl_sl := by
  intro ce v1 v2 v m
  rw [eq_lt_sl_sl, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmp_long_lt x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_lt_sl_1 x y (by omega)
    · exact .bo_lt_sl_0 x y (by omega)
  · intro h
    cases h with
    | bo_lt_sl_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmp_long_lt x y) (by simp only [holds]; omega)]
    | bo_lt_sl_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmp_long_lt x y) (by simp only [holds]; omega)]

theorem eq_le_sl_sl (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Ole v1 tsl v2 tsl m = onLongs (fun x y =>
      some (Val.of_bool (LClight.Int64.cmp .Cle x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem le_sl_sl : stmt_le_sl_sl := by
  intro ce v1 v2 v m
  rw [eq_le_sl_sl, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmp_long_le x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_le_sl_1 x y (by omega)
    · exact .bo_le_sl_0 x y (by omega)
  · intro h
    cases h with
    | bo_le_sl_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmp_long_le x y) (by simp only [holds]; omega)]
    | bo_le_sl_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmp_long_le x y) (by simp only [holds]; omega)]

theorem eq_shr_sl_ul (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oshr v1 tsl v2 tul m = onLongs (fun x y =>
      if LClight.Int64.ltu y LClight.Int64.iwordsize then some (.Vlong (LClight.Int64.shr x y))
      else none) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem shr_sl_ul : stmt_shr_sl_ul := by
  intro ce v1 v2 v m
  rw [eq_shr_sl_ul, onLongs_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · rename_i hy
      obtain rfl := Option.some.inj h
      have hy' := (long_ltu_64 y).1 hy
      rw [long_shr x y hy']
      exact .bo_shr_sl_ul x y hy'
    · cases h
  · intro h
    cases h with
    | bo_shr_sl_ul x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_left ((long_ltu_64 y).2 hy), long_shr x y hy]

/-! ## Operators on unsigned int -/

theorem eq_add_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oadd v1 tui v2 tui m = onInts (fun x y =>
      some (.Vint (r32 (u32 x + u32 y)))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem add_ui_ui : stmt_add_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_add_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .bo_add_ui x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

theorem eq_sub_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Osub v1 tui v2 tui m = onInts (fun x y =>
      some (.Vint (r32 (u32 x - u32 y)))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem sub_ui_ui : stmt_sub_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_sub_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .bo_sub_ui x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, rfl⟩

theorem eq_and_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oand v1 tui v2 tui m = onInts (fun x y =>
      some (.Vint (LClight.Int.and x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem and_ui_ui : stmt_and_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_and_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rw [int_and]
    exact .bo_and_ui x y
  · intro h
    cases h
    exact ⟨_, _, rfl, rfl, by rw [int_and]⟩

theorem eq_shl_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oshl v1 tui v2 tui m = onInts (fun x y =>
      if LClight.Int.ltu y LClight.Int.iwordsize then some (.Vint (LClight.Int.shl x y))
      else none) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem shl_ui_ui : stmt_shl_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_shl_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · rename_i hy
      obtain rfl := Option.some.inj h
      have hy' := (int_ltu_32 y).1 hy
      rw [int_shl x y hy']
      exact .bo_shl_ui x y hy'
    · cases h
  · intro h
    cases h with
    | bo_shl_ui x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_left ((int_ltu_32 y).2 hy), int_shl x y hy]

theorem eq_shr_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oshr v1 tui v2 tui m = onInts (fun x y =>
      if LClight.Int.ltu y LClight.Int.iwordsize then some (.Vint (LClight.Int.shru x y))
      else none) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem shr_ui_ui : stmt_shr_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_shr_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    split at h
    · rename_i hy
      obtain rfl := Option.some.inj h
      have hy' := (int_ltu_32 y).1 hy
      rw [int_shru x y hy']
      exact .bo_shr_ui x y hy'
    · cases h
  · intro h
    cases h with
    | bo_shr_ui x y hy =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [ite_eq_left ((int_ltu_32 y).2 hy), int_shru x y hy]

theorem eq_eq_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oeq v1 tui v2 tui m = onInts (fun x y =>
      some (Val.of_bool (LClight.Int.cmpu .Ceq x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem eq_ui_ui : stmt_eq_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_eq_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_int .Ceq x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_eq_ui_1 x y (by omega)
    · exact .bo_eq_ui_0 x y (by omega)
  · intro h
    cases h with
    | bo_eq_ui_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_int .Ceq x y) (by simp only [holds]; omega)]
    | bo_eq_ui_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_int .Ceq x y) (by simp only [holds]; omega)]

theorem eq_ne_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .One v1 tui v2 tui m = onInts (fun x y =>
      some (Val.of_bool (LClight.Int.cmpu .Cne x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem ne_ui_ui : stmt_ne_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_ne_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_int .Cne x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_ne_ui_1 x y (by omega)
    · exact .bo_ne_ui_0 x y (by omega)
  · intro h
    cases h with
    | bo_ne_ui_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_int .Cne x y) (by simp only [holds]; omega)]
    | bo_ne_ui_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_int .Cne x y) (by simp only [holds]; omega)]

theorem eq_lt_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Olt v1 tui v2 tui m = onInts (fun x y =>
      some (Val.of_bool (LClight.Int.cmpu .Clt x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem lt_ui_ui : stmt_lt_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_lt_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_int .Clt x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_lt_ui_1 x y (by omega)
    · exact .bo_lt_ui_0 x y (by omega)
  · intro h
    cases h with
    | bo_lt_ui_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_int .Clt x y) (by simp only [holds]; omega)]
    | bo_lt_ui_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_int .Clt x y) (by simp only [holds]; omega)]

theorem eq_gt_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Ogt v1 tui v2 tui m = onInts (fun x y =>
      some (Val.of_bool (LClight.Int.cmpu .Cgt x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem gt_ui_ui : stmt_gt_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_gt_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_int .Cgt x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_gt_ui_1 x y (by omega)
    · exact .bo_gt_ui_0 x y (by omega)
  · intro h
    cases h with
    | bo_gt_ui_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_int .Cgt x y) (by simp only [holds]; omega)]
    | bo_gt_ui_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_int .Cgt x y) (by simp only [holds]; omega)]

theorem eq_ge_ui_ui (ce : Unit) (v1 v2 : val) (m : mem) :
    sem_binop ce .Oge v1 tui v2 tui m = onInts (fun x y =>
      some (Val.of_bool (LClight.Int.cmpu .Cge x y))) v1 v2 := by
  cases v1 <;> cases v2 <;> rfl

theorem ge_ui_ui : stmt_ge_ui_ui := by
  intro ce v1 v2 v m
  rw [eq_ge_ui_ui, onInts_some]
  constructor
  · rintro ⟨x, y, rfl, rfl, h⟩
    obtain rfl := Option.some.inj h
    rcases of_bool_cases (cmpu_int .Cge x y) with ⟨hp, he⟩ | ⟨hp, he⟩ <;> rw [he] <;>
      simp only [holds] at hp
    · exact .bo_ge_ui_1 x y (by omega)
    · exact .bo_ge_ui_0 x y (by omega)
  · intro h
    cases h with
    | bo_ge_ui_1 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_one (cmpu_int .Cge x y) (by simp only [holds]; omega)]
    | bo_ge_ui_0 x y hp =>
        refine ⟨x, y, rfl, rfl, ?_⟩
        rw [of_bool_zero (cmpu_int .Cge x y) (by simp only [holds]; omega)]

/-! ## Casts -/

theorem eq_cast_si_ui (v1 : val) (m : mem) :
    sem_cast v1 tsi tui m = onInt (fun x => some (.Vint x)) v1 := by
  cases v1 <;> rfl

theorem cast_si_ui : stmt_cast_si_ui := by
  intro v1 v m
  rw [eq_cast_si_ui, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_si_ui x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ui_si (v1 : val) (m : mem) :
    sem_cast v1 tui tsi m = onInt (fun x => some (.Vint x)) v1 := by
  cases v1 <;> rfl

theorem cast_ui_si : stmt_cast_ui_si := by
  intro v1 v m
  rw [eq_cast_ui_si, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_ui_si x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ul_ui (v1 : val) (m : mem) :
    sem_cast v1 tul tui m = onLong (fun x => some (.Vint (r32 (u64 x)))) v1 := by
  cases v1 <;> rfl

theorem cast_ul_ui : stmt_cast_ul_ui := by
  intro v1 v m
  rw [eq_cast_ul_ui, onLong_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_ul_ui x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ui_ul (v1 : val) (m : mem) :
    sem_cast v1 tui tul m = onInt (fun x => some (.Vlong (r64 (u32 x)))) v1 := by
  cases v1 <;> rfl

theorem cast_ui_ul : stmt_cast_ui_ul := by
  intro v1 v m
  rw [eq_cast_ui_ul, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_ui_ul x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ul_sl (v1 : val) (m : mem) :
    sem_cast v1 tul tsl m = passLong v1 := by
  cases v1 <;> rfl

theorem cast_ul_sl : stmt_cast_ul_sl := by
  intro v1 v m
  rw [eq_cast_ul_sl]
  constructor
  · intro h
    cases v1 <;> cases h
    · exact .co_ul_sl _
    · exact .co_ul_sl_ptr _ _
  · intro h
    cases h <;> rfl

theorem eq_cast_sl_ul (v1 : val) (m : mem) :
    sem_cast v1 tsl tul m = passLong v1 := by
  cases v1 <;> rfl

theorem cast_sl_ul : stmt_cast_sl_ul := by
  intro v1 v m
  rw [eq_cast_sl_ul]
  constructor
  · intro h
    cases v1 <;> cases h
    · exact .co_sl_ul _
    · exact .co_sl_ul_ptr _ _
  · intro h
    cases h <;> rfl

theorem eq_cast_uc_ul (v1 : val) (m : mem) :
    sem_cast v1 tuc tul m = onInt (fun x => some (.Vlong (r64 (u32 x)))) v1 := by
  cases v1 <;> rfl

theorem cast_uc_ul : stmt_cast_uc_ul := by
  intro v1 v m
  rw [eq_cast_uc_ul, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_uc_ul x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_uc_ui (v1 : val) (m : mem) :
    sem_cast v1 tuc tui m = onInt (fun x => some (.Vint x)) v1 := by
  cases v1 <;> rfl

theorem cast_uc_ui : stmt_cast_uc_ui := by
  intro v1 v m
  rw [eq_cast_uc_ui, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_uc_ui x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ul_uc (v1 : val) (m : mem) :
    sem_cast v1 tul tuc m = onLong (fun x =>
      some (.Vint (LClight.Int.zero_ext 8 (LClight.Int.repr (LClight.Int64.unsigned x)))))
      v1 := by
  cases v1 <;> rfl

theorem cast_ul_uc : stmt_cast_ul_uc := by
  intro v1 v m
  rw [eq_cast_ul_uc, onLong_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    rw [zero_ext8_long]
    exact .co_ul_uc x
  · intro h
    cases h
    exact ⟨_, rfl, by rw [zero_ext8_long]⟩

theorem eq_cast_ui_uc (v1 : val) (m : mem) :
    sem_cast v1 tui tuc m = onInt (fun x => some (.Vint (r32 (zmod (u32 x) 256)))) v1 := by
  cases v1 <;> rfl

theorem cast_ui_uc : stmt_cast_ui_uc := by
  intro v1 v m
  rw [eq_cast_ui_uc, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_ui_uc x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_vuc_ul (v1 : val) (m : mem) :
    sem_cast v1 tvuc tul m = onInt (fun x => some (.Vlong (r64 (u32 x)))) v1 := by
  cases v1 <;> rfl

theorem cast_vuc_ul : stmt_cast_vuc_ul := by
  intro v1 v m
  rw [eq_cast_vuc_ul, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_vuc_ul x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_vui_ul (v1 : val) (m : mem) :
    sem_cast v1 tvui tul m = onInt (fun x => some (.Vlong (r64 (u32 x)))) v1 := by
  cases v1 <;> rfl

theorem cast_vui_ul : stmt_cast_vui_ul := by
  intro v1 v m
  rw [eq_cast_vui_ul, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_vui_ul x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ui_vui (v1 : val) (m : mem) :
    sem_cast v1 tui tvui m = onInt (fun x => some (.Vint x)) v1 := by
  cases v1 <;> rfl

theorem cast_ui_vui : stmt_cast_ui_vui := by
  intro v1 v m
  rw [eq_cast_ui_vui, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_ui_vui x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_ul_ul (v1 : val) (m : mem) :
    sem_cast v1 tul tul m = passLong v1 := by
  cases v1 <;> rfl

theorem cast_ul_ul : stmt_cast_ul_ul := by
  intro v1 v m
  rw [eq_cast_ul_ul]
  constructor
  · intro h
    cases v1 <;> cases h
    · exact .co_ul_ul _
    · exact .co_ul_ul_ptr _ _
  · intro h
    cases h <;> rfl

theorem eq_cast_ui_ui (v1 : val) (m : mem) :
    sem_cast v1 tui tui m = onInt (fun x => some (.Vint x)) v1 := by
  cases v1 <;> rfl

theorem cast_ui_ui : stmt_cast_ui_ui := by
  intro v1 v m
  rw [eq_cast_ui_ui, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_ui_ui x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_uc_uc (v1 : val) (m : mem) :
    sem_cast v1 tuc tuc m = onInt (fun x => some (.Vint (r32 (zmod (u32 x) 256)))) v1 := by
  cases v1 <;> rfl

theorem cast_uc_uc : stmt_cast_uc_uc := by
  intro v1 v m
  rw [eq_cast_uc_uc, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_uc_uc x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

theorem eq_cast_si_si (v1 : val) (m : mem) :
    sem_cast v1 tsi tsi m = onInt (fun x => some (.Vint x)) v1 := by
  cases v1 <;> rfl

theorem cast_si_si : stmt_cast_si_si := by
  intro v1 v m
  rw [eq_cast_si_si, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    exact .co_si_si x
  · intro h
    cases h
    exact ⟨_, rfl, rfl⟩

/-! ## Conditions -/

theorem eq_bool_si (v : val) (m : mem) :
    bool_val v tsi m =
      onInt (fun x => some (!LClight.Int.eq x LClight.Int.zero)) v := by
  cases v <;> rfl

theorem bool_si : stmt_bool_si := by
  intro v b m
  rw [eq_bool_si, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    cases hb : LClight.Int.eq x LClight.Int.zero
    · exact .bv_si_true x fun e => by rw [(int_eq_zero x).2 e] at hb; cases hb
    · exact .bv_si_false x ((int_eq_zero x).1 hb)
  · intro h
    cases h with
    | bv_si_true x hx =>
        refine ⟨x, rfl, ?_⟩
        have hb : LClight.Int.eq x LClight.Int.zero = false :=
          Bool.eq_false_iff.mpr fun e => hx ((int_eq_zero x).1 e)
        rw [hb]
        rfl
    | bv_si_false x hx =>
        refine ⟨x, rfl, ?_⟩
        rw [(int_eq_zero x).2 hx]
        rfl

theorem eq_bool_ui (v : val) (m : mem) :
    bool_val v tui m =
      onInt (fun x => some (!LClight.Int.eq x LClight.Int.zero)) v := by
  cases v <;> rfl

theorem bool_ui : stmt_bool_ui := by
  intro v b m
  rw [eq_bool_ui, onInt_some]
  constructor
  · rintro ⟨x, rfl, h⟩
    obtain rfl := Option.some.inj h
    cases hb : LClight.Int.eq x LClight.Int.zero
    · exact .bv_ui_true x fun e => by rw [(int_eq_zero x).2 e] at hb; cases hb
    · exact .bv_ui_false x ((int_eq_zero x).1 hb)
  · intro h
    cases h with
    | bv_ui_true x hx =>
        refine ⟨x, rfl, ?_⟩
        have hb : LClight.Int.eq x LClight.Int.zero = false :=
          Bool.eq_false_iff.mpr fun e => hx ((int_eq_zero x).1 e)
        rw [hb]
        rfl
    | bv_ui_false x hx =>
        refine ⟨x, rfl, ?_⟩
        rw [(int_eq_zero x).2 hx]
        rfl

/-! ## Constants -/

theorem const_int : stmt_const_int := by
  intro ge e le m i ty v
  constructor
  · intro h
    cases h with
    | eval_Econst_int => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · rintro rfl
    exact .eval_Econst_int _ _

theorem const_long : stmt_const_long := by
  intro ge e le m i ty v
  constructor
  · intro h
    cases h with
    | eval_Econst_long => rfl
    | eval_Elvalue _ _ _ _ _ hl _ => cases hl
  · rintro rfl
    exact .eval_Econst_long _ _

end ClightN.Proof
