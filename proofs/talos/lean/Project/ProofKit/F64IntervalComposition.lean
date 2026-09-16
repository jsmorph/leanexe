import Project.ProofKit.F64IntervalSpec

namespace Project.ProofKit.F64Interval
open CodeLib.IEEE64

def Valid (result : Bounds) (x : ℝ) : Prop := result.status = 0 → Sound result x

theorem guard_accepted (ok : Bool) (result : Bounds)
    (h : (if ok then result else rejected).status = 0) :
    ok = true ∧ result.status = 0 := by
  cases ok <;> simp_all [rejected]

theorem point_valid (word : UInt64) : Valid (point word) (value word) := by
  intro h
  have hf := (guard_accepted (F64Order.finiteBits word) ⟨0, word, word⟩ h).1
  exact point_sound word ((F64Order.finiteBits_iff word).mp hf)

theorem Valid.add {a b : Bounds} {x y : ℝ} (ha : Valid a x) (hb : Valid b y) :
    Valid (add a b) (x + y) := by
  intro h
  have hg := (guard_accepted (a.status == 0 && b.status == 0)
    (pack (F64Outward.add false a.lower b.lower) (F64Outward.add true a.upper b.upper)) h).1
  have hp : a.status = 0 ∧ b.status = 0 := by simpa using hg
  exact add_sound a b x y (ha hp.1) (hb hp.2) h

theorem Valid.sub {a b : Bounds} {x y : ℝ} (ha : Valid a x) (hb : Valid b y) :
    Valid (sub a b) (x - y) := by
  intro h
  have hg := (guard_accepted (a.status == 0 && b.status == 0)
    (pack (F64Outward.sub false a.lower b.upper) (F64Outward.sub true a.upper b.lower)) h).1
  have hp : a.status = 0 ∧ b.status = 0 := by simpa using hg
  exact sub_sound a b x y (ha hp.1) (hb hp.2) h

theorem Valid.scale {a : Bounds} {x : ℝ} (ha : Valid a x) (word : UInt64) :
    Valid (scale a word) (x * value word) := by
  intro h
  have hg := (guard_accepted (a.status == 0)
    (if word < 0x8000000000000000 then
      pack (F64Outward.mul false a.lower word) (F64Outward.mul true a.upper word)
    else pack (F64Outward.mul false a.upper word) (F64Outward.mul true a.lower word)) h).1
  exact scale_sound a word x (ha (by simpa using hg)) h

theorem Valid.divPositive {a : Bounds} {x : ℝ} (ha : Valid a x) (word : UInt64) :
    Valid (divPositive a word) (x / value word) := by
  intro h
  have hg := (guard_accepted (a.status == 0 && F64Order.positiveBits word)
    (pack (F64Outward.div false a.lower word) (F64Outward.div true a.upper word)) h).1
  have hp : a.status = 0 ∧ F64Order.positiveBits word = true := by simpa using hg
  exact divPositive_sound a word x (ha hp.1) h

#print axioms point_valid
#print axioms Valid.add
#print axioms Valid.sub
#print axioms Valid.scale
#print axioms Valid.divPositive
end Project.ProofKit.F64Interval
