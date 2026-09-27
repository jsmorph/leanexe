import Project.SpectralKL.WordShader

namespace Project.SpectralKL.WordShader
open WordMoments

abbrev u (n : Nat) : UInt32 := UInt32.ofNat n

theorem u_nat (n : Nat) (h : n < 4294967296) : (u n).toNat = n :=
  UInt32.toNat_ofNat_of_lt' h

theorem address_bound (m r i : Nat) (hm : m ≤ 32) (hr : r < 1048576) (hi : i < m) :
    r*m+i < 33554432 := by
  have h := Nat.mul_le_mul_right m (show r+1 ≤ 1048576 by omega)
  nlinarith

theorem address_nat (m r i : Nat) (hm : m ≤ 32) (hr : r < 1048576) (hi : i < m) :
    (u r*u m+u i).toNat = r*m+i := by
  rw [← UInt32.ofNat_mul,← UInt32.ofNat_add]
  exact u_nat _ (by have h := address_bound m r i hm hr hi; omega)

theorem pair_bound (m i j : Nat) (hm : m ≤ 32) (hi : i < m) (hj : j < m) :
    i*m+j < m*m ∧ m+i*m+j < 1056 := by
  have h := Nat.mul_le_mul_right m (show i+1 ≤ m by omega)
  have hm2 := Nat.mul_le_mul hm hm
  constructor <;> nlinarith

theorem pair_column (m i j : Nat) (hm : m ≤ 32) (hi : i < m) (hj : j < m) :
    (u (m+i*m+j)-u m)/u m = u i ∧ (u (m+i*m+j)-u m)%u m = u j := by
  have hp := pair_bound m i j hm hi hj
  have hm0 : 0 < m := by omega
  have he : u (m+i*m+j)-u m = u (i*m+j) := by
    rw [← UInt32.ofNat_sub (show m ≤ m+i*m+j by omega)]
    congr 1
    omega
  rw [he]
  constructor
  · apply UInt32.toNat.inj
    rw [UInt32.toNat_div,u_nat _ (by omega),u_nat _ (by omega),u_nat _ (by omega)]
    rw [Nat.mul_comm i m,Nat.mul_add_div hm0,Nat.div_eq_of_lt hj]
    omega
  · apply UInt32.toNat.inj
    rw [UInt32.toNat_mod,u_nat _ (by omega),u_nat _ (by omega),u_nat _ (by omega)]
    exact Nat.mul_add_mod_of_lt hj

theorem mean_term (input : Nat → UInt32) (m r i : Nat)
    (hm : m ≤ 32) (hr : r < 1048576) (hi : i < m) :
    termAt kernel input (u m) (u i) (u r) = input (r*m+i) := by
  have hlt : u i < u m := by
    rw [UInt32.lt_iff_toNat_lt,u_nat _ (by omega),u_nat _ (by omega)]
    exact hi
  simp only [termAt,hlt,ite_true,kernel,address,Expr.eval,Env.get,Op.eval]
  rw [address_nat m r i hm hr hi]

theorem product_term (input : Nat → UInt32) (m r i j : Nat)
    (hm : m ≤ 32) (hr : r < 1048576) (hi : i < m) (hj : j < m) :
    termAt kernel input (u m) (u (m+i*m+j)) (u r) =
      input (r*m+i)*input (r*m+j) := by
  have hp := pair_bound m i j hm hi hj
  have hlt : ¬ u (m+i*m+j) < u m := by
    rw [UInt32.lt_iff_toNat_lt,u_nat _ (by omega),u_nat _ (by omega)]
    omega
  simp only [termAt,hlt,ite_false,kernel,address,Expr.eval,Env.get,Op.eval]
  rw [(pair_column m i j hm hi hj).1,(pair_column m i j hm hi hj).2,
    address_nat m r i hm hr hi,address_nat m r j hm hr hj]

/-- The uploaded buffer is the supplied biased observation matrix in row order. -/
def Layout {m : Nat} (input : Nat → UInt32) (rows : List (Fin m → Sample)) : Prop :=
  ∀ r (hr : r < rows.length) (i : Fin m), input (r*m+i.val) = word (rows[r] i)

theorem map_range_eq {α β : Type*} (rows : List α) (f : Nat → β) (g : α → β)
    (h : ∀ r (hr : r < rows.length), f r = g rows[r]) :
    (List.range rows.length).map f = rows.map g := by
  apply List.ext_getElem
  · simp
  · intro r hr hs
    simp only [List.getElem_map,List.getElem_range]
    exact h r (by simpa using hr)

theorem run_column {m : Nat} (input : Nat → UInt32) (rows : List (Fin m → Sample))
    (hm : m ≤ 32) (hn : rows.length ≤ 1048576) (hl : Layout input rows) (i : Fin m) :
    run kernel input (u m) (u i.val) (u rows.length) = column rows i := by
  rw [run_eq_reduce,u_nat _ (by omega)]
  unfold column
  congr 1
  apply map_range_eq
  intro r hr
  rw [mean_term input m r i.val hm (by omega) i.isLt,hl r hr i]

theorem run_product {m : Nat} (input : Nat → UInt32) (rows : List (Fin m → Sample))
    (hm : m ≤ 32) (hn : rows.length ≤ 1048576) (hl : Layout input rows) (i j : Fin m) :
    run kernel input (u m) (u (m+i.val*m+j.val)) (u rows.length) = gram rows i j := by
  rw [run_eq_reduce,u_nat _ (by omega)]
  unfold gram
  congr 1
  apply map_range_eq
  intro r hr
  rw [product_term input m r i.val j.val hm (by omega) i.isLt j.isLt,hl r hr i,hl r hr j]

/-- Distinct active invocation IDs write distinct vec2 output elements. -/
theorem distinct_outputs (a b : Nat) (h : a ≠ b) : 8*a ≠ 8*b := by omega

theorem mean_output_bound {m : Nat} (i : Fin m) : i.val < m+m*m := by omega
theorem product_output_bound {m : Nat} (i j : Fin m) : m+i.val*m+j.val < m+m*m := by
  have h := Nat.mul_le_mul_right m (show i.val+1 ≤ m by omega)
  have hj := j.isLt
  nlinarith

theorem dispatch_covers (entry entries : Nat) (h : entry < entries) :
    entry/64 < (entries+63)/64 ∧ entry%64 < 64 := by omega

theorem input_index_bound (m count r i : Nat) (hr : r < count) (hi : i < m) :
    r*m+i < count*m := by
  have h := Nat.mul_le_mul_right m (show r+1 ≤ count by omega)
  nlinarith

theorem active_entry (m entry : Nat) (hm : 0 < m) (h : entry < m+m*m) :
    entry < m ∨ ∃ i j, i < m ∧ j < m ∧ entry = m+i*m+j := by
  by_cases he : entry < m
  · exact Or.inl he
  · right
    refine ⟨(entry-m)/m,(entry-m)%m,?_,Nat.mod_lt _ hm,?_⟩
    · apply (Nat.div_lt_iff_lt_mul hm).mpr
      omega
    · have hd := Nat.mod_add_div (entry-m) m
      rw [Nat.mul_comm m] at hd
      omega

theorem row_counter (r count : Nat) (hc : count ≤ 1048576) (hr : r < count) :
    u r < u count ∧ (u r+1).toNat = r+1 := by
  constructor
  · rw [UInt32.lt_iff_toNat_lt,u_nat _ (by omega),u_nat _ (by omega)]
    exact hr
  · change (u r+u 1).toNat = r+1
    rw [← UInt32.ofNat_add]
    exact u_nat _ (by omega)

#print axioms run_column
#print axioms run_product
end Project.SpectralKL.WordShader
