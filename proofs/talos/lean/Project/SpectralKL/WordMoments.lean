import Project.SpectralKL.MatrixAuto

namespace Project.SpectralKL.WordMoments

/-- Two u32 limbs, matching the arithmetic available in a WGSL compute invocation. -/
structure Sum64 where
  lo : UInt32
  hi : UInt32
deriving Repr, DecidableEq

def Sum64.value (s : Sum64) : Nat := s.lo.toNat+4294967296*s.hi.toNat

def addWord (s : Sum64) (v : UInt32) : Sum64 :=
  let lo := s.lo+v
  let carry : UInt32 := if lo < s.lo then 1 else 0
  ⟨lo,s.hi+carry⟩

theorem addWord_value (s : Sum64) (v : UInt32)
    (h : s.value+v.toNat < 18446744073709551616) :
    (addWord s v).value = s.value+v.toNat := by
  have hl := s.lo.toNat_lt
  have hv := v.toNat_lt
  have hh := s.hi.toNat_lt
  norm_num at hl hv hh
  have hs : (s.lo+v).toNat = (s.lo.toNat+v.toNat)%4294967296 := by
    rw [UInt32.toNat_add]
  unfold Sum64.value at h ⊢
  by_cases hc : 4294967296 ≤ s.lo.toNat+v.toNat
  · have hlo : (s.lo+v).toNat = s.lo.toNat+v.toNat-4294967296 := by omega
    have hcarry : s.lo+v < s.lo := UInt32.lt_iff_toNat_lt.mpr (by omega)
    have hhi : (s.hi+(1:UInt32)).toNat = s.hi.toNat+1 := by
      rw [UInt32.toNat_add]
      norm_num [UInt32.toNat_ofNat]
      omega
    simp only [addWord,hcarry,ite_true,hlo,hhi]
    omega
  · have hlo : (s.lo+v).toNat = s.lo.toNat+v.toNat := by omega
    have hcarry : ¬ s.lo+v < s.lo := by rw [UInt32.lt_iff_toNat_lt]; omega
    simp only [addWord,hcarry,ite_false,UInt32.add_zero,hlo]
    omega

def reduce (values : List UInt32) : Sum64 := values.foldl addWord ⟨0,0⟩

theorem fold_value (values : List UInt32) (s : Sum64)
    (h : s.value+(values.map UInt32.toNat).sum < 18446744073709551616) :
    (values.foldl addWord s).value = s.value+(values.map UInt32.toNat).sum := by
  induction values generalizing s with
  | nil => simp
  | cons v vs ih =>
    simp only [List.map_cons,List.sum_cons] at h ⊢
    have ha : s.value+v.toNat < 18446744073709551616 := by omega
    have he := addWord_value s v ha
    rw [List.foldl_cons,ih (addWord s v) (by rw [he]; omega),he]
    omega

theorem reduce_value (values : List UInt32)
    (h : (values.map UInt32.toNat).sum < 18446744073709551616) :
    (reduce values).value = (values.map UInt32.toNat).sum := by
  simpa [reduce,Sum64.value] using fold_value values ⟨0,0⟩ (by simpa [Sum64.value] using h)

theorem sum_bound (values : List UInt32) :
    (values.map UInt32.toNat).sum ≤ values.length*4294967295 := by
  induction values with
  | nil => simp
  | cons v vs ih =>
    have hv := v.toNat_lt
    norm_num at hv
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

theorem reduce_exact (values : List UInt32) (h : values.length ≤ 1048576) :
    (reduce values).value = (values.map UInt32.toNat).sum := by
  apply reduce_value
  have hs := sum_bound values
  nlinarith

/-- Biased signed 16-bit input. Decoding below subtracts 32768 exactly. -/
abbrev Sample := Fin 65536

def word (x : Sample) : UInt32 := UInt32.ofNat x.val
@[simp] theorem word_value (x : Sample) : (word x).toNat = x.val := by
  apply UInt32.toNat_ofNat_of_lt'
  have h := x.isLt
  norm_num [UInt32.size]
  omega

theorem product_value (x y : Sample) : (word x*word y).toNat = x.val*y.val := by
  rw [UInt32.toNat_mul,word_value,word_value]
  apply Nat.mod_eq_of_lt
  have hx := x.isLt
  have hy := y.isLt
  norm_num
  nlinarith [Nat.mul_le_mul (show x.val ≤ 65535 by omega) (show y.val ≤ 65535 by omega)]

variable {m : Nat}
def column (rows : List (Fin m → Sample)) (i : Fin m) : Sum64 :=
  reduce (rows.map fun v => word (v i))
def gram (rows : List (Fin m → Sample)) (i j : Fin m) : Sum64 :=
  reduce (rows.map fun v => word (v i)*word (v j))

theorem column_value (rows : List (Fin m → Sample)) (h : rows.length ≤ 1048576) (i : Fin m) :
    (column rows i).value = (rows.map fun v => (v i).val).sum := by
  rw [column,reduce_exact _ (by simpa using h)]
  simp [List.map_map,Function.comp_def]

theorem gram_value (rows : List (Fin m → Sample)) (h : rows.length ≤ 1048576) (i j : Fin m) :
    (gram rows i j).value = (rows.map fun v => (v i).val*(v j).val).sum := by
  rw [gram,reduce_exact _ (by simpa using h)]
  simp only [List.map_map,Function.comp_def,product_value]

#print axioms column_value
#print axioms gram_value
end Project.SpectralKL.WordMoments
