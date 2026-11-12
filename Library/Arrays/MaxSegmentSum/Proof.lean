import Library.Arrays.MaxSegmentSum.Program
import Library.Arrays.MaxSegmentSum.Spec

/-! The proof that `mss` computes `maxSegmentSum` of its elements read as integers when their
absolute values sum to less than `2^63`.  The proof follows the fold from the left.  After a prefix
`p` of the elements, `best` is `maxSegmentSum p` and `ending` is `maxSuffixSum p`, the greatest sum
of a suffix of `p`, the empty suffix included.  The suffixes of `p ++ [x]` are the suffixes of `p`
with `x` appended and the empty list, so `maxSuffixSum (p ++ [x])` is
`max (maxSuffixSum p + x) 0` (`maxSuffixSum_append_singleton`).  The segments of `p ++ [x]` are
those of `p` and the suffixes of `p ++ [x]`, so `maxSegmentSum (p ++ [x])` is
`max (maxSegmentSum p) (maxSuffixSum (p ++ [x]))` (`maxSegmentSum_append_singleton`).  These
equations are the program's step over ℤ.  The invariant also bounds `ending` by the sum of the
absolute values of `p`, so no `Int64` sum of the program wraps. -/

namespace Library.Arrays.MaxSegmentSum

/-- The greatest sum of a suffix of `xs`, the empty suffix included. -/
def maxSuffixSum (xs : List Int) : Int := (xs.tails.map List.sum).foldr max 0

theorem foldr_max_max (b c : Int) : ∀ l : List Int, l.foldr max (max b c) = max b (l.foldr max c)
  | [] => rfl
  | a :: l => by
    simp only [List.foldr_cons, foldr_max_max b c l]
    omega

theorem le_foldr_max (b : Int) : ∀ l : List Int, b ≤ l.foldr max b
  | [] => Int.le_refl b
  | a :: l => by
    have := le_foldr_max b l
    simp only [List.foldr_cons]
    omega

theorem le_foldr_max_of_mem {a : Int} (b : Int) : ∀ {l : List Int}, a ∈ l → a ≤ l.foldr max b
  | c :: l, h => by
    simp only [List.foldr_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_foldr_max_of_mem b h
      omega

theorem foldr_max_add (b x : Int) :
    ∀ l : List Int, (l.map (· + x)).foldr max (b + x) = l.foldr max b + x
  | [] => rfl
  | a :: l => by
    simp only [List.map_cons, List.foldr_cons, foldr_max_add b x l]
    omega

theorem nil_mem_tails {α : Type} : ∀ l : List α, [] ∈ l.tails
  | [] => List.mem_singleton_self []
  | _ :: l => List.mem_cons_of_mem _ (nil_mem_tails l)

theorem tails_append_singleton {α : Type} (x : α) :
    ∀ l : List α, (l ++ [x]).tails = l.tails.map (· ++ [x]) ++ [[]]
  | [] => rfl
  | a :: l => by
    rw [List.cons_append, List.tails, tails_append_singleton x l, List.tails, List.map_cons,
      List.cons_append, List.cons_append]

theorem inits_append_singleton {α : Type} (x : α) :
    ∀ l : List α, (l ++ [x]).inits = l.inits ++ [l ++ [x]]
  | [] => rfl
  | a :: l => by
    rw [List.cons_append, List.inits, inits_append_singleton x l, List.inits, List.map_append,
      List.cons_append, List.map_singleton]

theorem maxSuffixSum_nonneg (xs : List Int) : 0 ≤ maxSuffixSum xs := le_foldr_max 0 _

theorem maxSuffixSum_append_singleton (p : List Int) (x : Int) :
    maxSuffixSum (p ++ [x]) = max (maxSuffixSum p + x) 0 := by
  have h0 : (0 : Int) ∈ p.tails.map List.sum := List.mem_map.mpr ⟨[], nil_mem_tails p, rfl⟩
  have hx : x ∈ (p.tails.map List.sum).map (· + x) :=
    List.mem_map.mpr ⟨0, h0, Int.zero_add x⟩
  have hl : (p ++ [x]).tails.map List.sum = (p.tails.map List.sum).map (· + x) ++ [0] := by
    simp [tails_append_singleton, Function.comp_def, List.sum_append]
  unfold maxSuffixSum
  rw [hl, List.foldr_append, show ([0] : List Int).foldr max 0 = 0 from rfl, ← foldr_max_add 0 x,
    Int.zero_add]
  have hle := le_foldr_max_of_mem 0 hx
  have e2 := foldr_max_max 0 x ((p.tails.map List.sum).map (· + x))
  have e3 := foldr_max_max x 0 ((p.tails.map List.sum).map (· + x))
  rw [Int.max_comm 0 x] at e2
  omega

theorem maxSegmentSum_append_singleton (p : List Int) (x : Int) :
    maxSegmentSum (p ++ [x]) = max (maxSegmentSum p) (maxSuffixSum (p ++ [x])) := by
  have hl : ((p ++ [x]).inits.map List.tails).flatten.map List.sum =
      (p.inits.map List.tails).flatten.map List.sum ++ (p ++ [x]).tails.map List.sum := by
    rw [inits_append_singleton, List.map_append, List.flatten_append, List.map_singleton,
      List.flatten_singleton, List.map_append]
  have he := maxSuffixSum_nonneg (p ++ [x])
  unfold maxSegmentSum
  rw [hl, List.foldr_append]
  unfold maxSuffixSum at he ⊢
  generalize ((p ++ [x]).tails.map List.sum).foldr max 0 = e at he ⊢
  have h := foldr_max_max e 0 ((p.inits.map List.tails).flatten.map List.sum)
  rw [show max e 0 = e by omega] at h
  omega

theorem toInt_max (a b : Int64) : (max a b).toInt = max a.toInt b.toInt := by
  rw [show max a b = if a ≤ b then b else a from rfl]
  split
  · rename_i h
    have := Int64.le_iff_toInt_le.mp h
    omega
  · rename_i h
    have := mt Int64.le_iff_toInt_le.mpr h
    omega

theorem toInt_add_of_bounds {a b : Int64} (h1 : -2 ^ 63 ≤ a.toInt + b.toInt)
    (h2 : a.toInt + b.toInt < 2 ^ 63) : (a + b).toInt = a.toInt + b.toInt := by
  rw [Int64.toInt_add]
  exact Int.bmod_eq_of_le_mul_two (by omega) (by omega)

/-- The step of `mss`'s fold. -/
def step (state : Int64 × Int64) (x : Int64) : Int64 × Int64 :=
  let ending := max (state.2 + x) 0
  (max state.1 ending, ending)

theorem mss_eq (xs : Array Int64) : mss xs = (xs.toList.foldl step (0, 0)).1 := by
  rw [mss, ← Array.foldl_toList]
  rfl

/-- The invariant of the fold after a prefix `p`: `best` is `maxSegmentSum p`, and `ending` is
`maxSuffixSum p` and at most the sum of the absolute values of `p`. -/
def Inv (p : List Int64) (state : Int64 × Int64) : Prop :=
  state.1.toInt = maxSegmentSum (p.map Int64.toInt) ∧
    state.2.toInt = maxSuffixSum (p.map Int64.toInt) ∧
    state.2.toInt ≤ (((p.map fun y => y.toInt.natAbs).sum : Nat) : Int)

theorem inv_step {p : List Int64} {x : Int64} {state : Int64 × Int64}
    (hb : ((p ++ [x]).map fun y => y.toInt.natAbs).sum < 2 ^ 63) (h : Inv p state) :
    Inv (p ++ [x]) (step state x) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hs : ((p ++ [x]).map fun y => y.toInt.natAbs).sum =
      (p.map fun y => y.toInt.natAbs).sum + x.toInt.natAbs := by
    simp [List.sum_append]
  have hm : (p ++ [x]).map Int64.toInt = p.map Int64.toInt ++ [x.toInt] := by simp
  have h0 := maxSuffixSum_nonneg (p.map Int64.toInt)
  have hadd : (state.2 + x).toInt = state.2.toInt + x.toInt :=
    toInt_add_of_bounds (by omega) (by omega)
  have he : (max (state.2 + x) 0).toInt = maxSuffixSum ((p ++ [x]).map Int64.toInt) := by
    rw [toInt_max, hadd, Int64.toInt_zero, hm, maxSuffixSum_append_singleton, ← h2]
  refine ⟨?_, he, ?_⟩
  · show (max state.1 (max (state.2 + x) 0)).toInt = _
    rw [toInt_max, he, h1, hm, maxSegmentSum_append_singleton]
  · show (max (state.2 + x) 0).toInt ≤ _
    rw [toInt_max, hadd, Int64.toInt_zero, hs]
    omega

theorem inv_foldl : ∀ (l p : List Int64) (state : Int64 × Int64),
    ((p ++ l).map fun y => y.toInt.natAbs).sum < 2 ^ 63 → Inv p state →
      Inv (p ++ l) (l.foldl step state)
  | [], p, state, _, h => by rw [List.append_nil]; exact h
  | x :: l, p, state, hb, h => by
    have hx : ((p ++ [x]).map fun y => y.toInt.natAbs).sum < 2 ^ 63 := by
      have hb2 := hb
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil] at hb2 ⊢
      omega
    have e : p ++ [x] ++ l = p ++ x :: l := by rw [List.append_assoc, List.singleton_append]
    have := inv_foldl l (p ++ [x]) (step state x) (by rw [e]; exact hb) (inv_step hx h)
    rw [e] at this
    exact this

/-- `mss` computes the maximum segment sum of its elements read as integers when their absolute
values sum to less than `2^63`. -/
theorem mss_toInt (xs : Array Int64) (h : (xs.toList.map fun x => x.toInt.natAbs).sum < 2 ^ 63) :
    (mss xs).toInt = maxSegmentSum (xs.toList.map Int64.toInt) := by
  have h0 : Inv [] ((0 : Int64), (0 : Int64)) := ⟨by decide, by decide, by decide⟩
  have := (inv_foldl xs.toList [] (0, 0) (by rwa [List.nil_append]) h0).1
  rw [List.nil_append] at this
  rw [mss_eq]
  exact this

end Library.Arrays.MaxSegmentSum
