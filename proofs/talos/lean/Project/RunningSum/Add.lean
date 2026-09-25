import Project.RunningSum.Compare

namespace Project.RunningSum

open LeanExe.Examples.RunningSum (Decimal add)

theorem add_correct (a b : Decimal) (ha : Canonical a.digits) (hb : Canonical b.digits) :
    Canonical (add a b).digits ∧ integer (add a b) = integer a + integer b := by
  unfold add
  simp only [magnitudeLess_correct a.digits b.digits ha hb, beq_iff_eq, decide_eq_true_eq]
  split_ifs with hsign hlt
  · obtain ⟨hc, hv⟩ := combine_add a.digits b.digits ha.1 hb.1
    refine ⟨hc, ?_⟩
    cases hsa : a.negative <;> cases hsb : b.negative <;> simp_all [integer, add_comm]
  · obtain ⟨hc, hv⟩ := combine_sub b.digits a.digits hb.1 ha.1 (by omega)
    refine ⟨hc, ?_⟩
    cases hsa : a.negative <;> cases hsb : b.negative <;> simp_all [integer] <;> omega
  · obtain ⟨hc, hv⟩ := combine_sub a.digits b.digits ha.1 hb.1 (by omega)
    refine ⟨hc, ?_⟩
    cases hsa : a.negative <;> cases hsb : b.negative <;> simp_all [integer] <;> omega

#print axioms add_correct

end Project.RunningSum
