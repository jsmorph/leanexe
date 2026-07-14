import Project.ClobFindBest.Loop

/-!
# The `findBest` theorem

The exported function returns the same optional index as the source search for
every well-laid-out order array.  The source theorem also states the price and
first-index properties of a successful result.
-/

namespace Project.ClobFindBest.Spec

open Wasm Project.Common Project.Clob Project.ClobFindBest
  Project.ClobFindBest.Model Project.ClobFindBest.Loop

set_option maxHeartbeats 64000000
set_option maxRecDepth 100000

/-- The public export returns the source search result and preserves the store. -/
@[spec_of "lean" "LeanExe.Examples.Clob.findBest"]
def ClobFindBestSpec : Prop :=
  ∀ (env : HostEnv Unit) (st : Store Unit) (ptr : UInt64)
    (os : List OrderL) (taker : OrderL),
    os.length < 4294967296 →
    OrdersAt st ptr os →
    TerminatesWith (m := «module») (id := 8) (initial := st) (env := env)
      [.i64 taker.oqty, .i64 taker.oprice, .i64 taker.oside,
       .i64 taker.otrader, .i64 taker.oid, .i64 ptr]
      (fun st' vs => vs = optionVals (findBestL os taker) ∧ st' = st)

@[proves Project.ClobFindBest.Spec.ClobFindBestSpec]
theorem findBest_correct : ClobFindBestSpec := by
  intro env st ptr os taker hlen hInput
  have hHead := hInput.1.1
  have hHeadB := hInput.1.2
  have hlen64 : os.length + 1 < UInt64.size := by
    rw [size_eq]
    omega
  have haddNat : (UInt64.ofNat os.length + 1).toNat =
      os.length + 1 := by
    rw [toNat_add_one]
    · rw [toNat_ofNat_lt]
      rw [size_eq]
      omega
    · rw [toNat_ofNat_lt (by rw [size_eq]; omega), size_eq]
      omega
  have hadd : UInt64.ofNat os.length + 1 =
      UInt64.ofNat (os.length + 1) := by
    apply UInt64.toNat.inj
    rw [haddNat, toNat_ofNat_lt hlen64]
  have hnowrap : ¬UInt64.ofNat os.length + 1 < UInt64.ofNat os.length := by
    rw [UInt64.lt_iff_toNat_lt, haddNat,
      toNat_ofNat_lt (by rw [size_eq]; omega)]
    omega
  apply TerminatesWith.of_wp_entry_for (f := func8Def)
  · simp [«module»]
  · change wp «module» func8 _ st
      { params := [.i64 ptr, .i64 taker.oid, .i64 taker.otrader,
          .i64 taker.oside, .i64 taker.oprice, .i64 taker.oqty],
        locals := [.i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
          .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0],
        values := [] } env
    unfold func8
    wp_run
    try simp
    rw [hHead]
    refine ⟨hHeadB, ?_⟩
    refine wp_iff_cons rfl ?_
    rw [if_neg (by simp [hnowrap])]
    norm_num
    rw [hadd]
    refine wp_call_tw (func7_spec env st ptr os taker hlen hInput) ?_
    rintro st' vs ⟨rfl, rfl⟩
    wp_run
    simp [func8Def, optionVals]

private abbrev atIndexL (os : List OrderL) (i : Nat) : OrderL :=
  os[i]!

def BestInPrefixL (os : List OrderL) (taker : OrderL) (k i : Nat) : Prop :=
  i < k ∧
  eligibleL taker (atIndexL os i) ∧
  ∀ q : Nat, q < k → eligibleL taker (atIndexL os q) →
    ¬betterPriceL taker (atIndexL os q) (atIndexL os i) ∧
    ((atIndexL os q).oprice = (atIndexL os i).oprice → i ≤ q)

private theorem betterPriceL_trans (taker a b c : OrderL) :
    betterPriceL taker a b →
    betterPriceL taker b c →
    betterPriceL taker a c := by
  by_cases hside : taker.oside = 0
  · simp only [betterPriceL, if_pos hside]
    intro hab hbc
    exact UInt64.lt_trans hab hbc
  · simp only [betterPriceL, if_neg hside]
    intro hab hbc
    exact UInt64.lt_trans hbc hab

private theorem bestPrefixL_spec (os : List OrderL) (taker : OrderL)
    (k : Nat) :
    (bestPrefixL os taker k = none →
      ∀ q : Nat, q < k → ¬eligibleL taker (atIndexL os q)) ∧
    (∀ i : Nat, bestPrefixL os taker k = some i →
      BestInPrefixL os taker k i) := by
  induction k with
  | zero =>
      constructor
      · intro _ q hq
        omega
      · intro i hi
        simp [bestPrefixL] at hi
  | succ k ih =>
      rcases ih with ⟨ihnone, ihSome⟩
      cases hprev : bestPrefixL os taker k with
      | none =>
          by_cases helig : eligibleL taker (atIndexL os k)
          · constructor
            · intro h
              rw [bestPrefixL, hprev] at h
              simp only [bestStepL] at h
              rw [if_pos helig] at h
              cases h
            · intro i hi
              have hiEq : i = k := by
                rw [bestPrefixL, hprev] at hi
                simp only [bestStepL] at hi
                rw [if_pos helig] at hi
                exact (Option.some.inj hi).symm
              subst i
              refine ⟨by omega, helig, ?_⟩
              intro q hq hqelig
              by_cases hqk : q = k
              · subst q
                exact ⟨by simp [betterPriceL], fun _ => Nat.le_refl _⟩
              · exact (ihnone hprev q (by omega) hqelig).elim
          · constructor
            · intro _ q hq hqelig
              by_cases hqk : q = k
              · subst q
                exact helig hqelig
              · exact ihnone hprev q (by omega) hqelig
            · intro i hi
              rw [bestPrefixL, hprev] at hi
              simp only [bestStepL] at hi
              rw [if_neg helig] at hi
              cases hi
      | some j =>
          have hj := ihSome j hprev
          rcases hj with ⟨hjlt, hjelig, hjbest⟩
          by_cases hchoose : eligibleL taker (atIndexL os k) ∧
              betterPriceL taker (atIndexL os k) (atIndexL os j)
          · constructor
            · intro h
              rw [bestPrefixL, hprev] at h
              simp only [bestStepL] at h
              rw [if_pos hchoose] at h
              cases h
            · intro i hi
              have hiEq : i = k := by
                rw [bestPrefixL, hprev] at hi
                simp only [bestStepL] at hi
                rw [if_pos hchoose] at hi
                exact (Option.some.inj hi).symm
              subst i
              refine ⟨by omega, hchoose.1, ?_⟩
              intro q hq hqelig
              by_cases hqk : q = k
              · subst q
                exact ⟨by simp [betterPriceL], fun _ => Nat.le_refl _⟩
              · have hqold := hjbest q (by omega) hqelig
                refine ⟨?_, ?_⟩
                · intro hqbetter
                  exact hqold.1
                    (betterPriceL_trans taker (atIndexL os q)
                      (atIndexL os k) (atIndexL os j)
                      hqbetter hchoose.2)
                · intro heq
                  have hqj : betterPriceL taker (atIndexL os q)
                      (atIndexL os j) := by
                    simpa only [betterPriceL, heq] using hchoose.2
                  exact (hqold.1 hqj).elim
          · constructor
            · intro h
              rw [bestPrefixL, hprev] at h
              simp only [bestStepL] at h
              rw [if_neg hchoose] at h
              cases h
            · intro i hi
              have hiEq : i = j := by
                rw [bestPrefixL, hprev] at hi
                simp only [bestStepL] at hi
                rw [if_neg hchoose] at hi
                exact (Option.some.inj hi).symm
              subst i
              refine ⟨by omega, hjelig, ?_⟩
              intro q hq hqelig
              by_cases hqk : q = k
              · subst q
                refine ⟨?_, fun _ => Nat.le_of_lt hjlt⟩
                intro hbetter
                exact hchoose ⟨hqelig, hbetter⟩
              · exact hjbest q (by omega) hqelig

/-- A successful search returns an eligible order at the best price.  Among
equal-price eligible orders, it returns the first array index. -/
theorem findBestL_best (os : List OrderL) (taker : OrderL) (i : Nat)
    (_hvalid : taker.oside = 0 ∨ taker.oside = 1)
    (hfound : findBestL os taker = some i) :
    i < os.length ∧
    eligibleL taker (atIndexL os i) ∧
    ∀ q : Nat, q < os.length →
      eligibleL taker (atIndexL os q) →
      ¬betterPriceL taker (atIndexL os q) (atIndexL os i) ∧
      ((atIndexL os q).oprice = (atIndexL os i).oprice →
        i ≤ q) := by
  rw [findBestL_eq_prefix] at hfound
  exact (bestPrefixL_spec os taker os.length).2 i hfound

end Project.ClobFindBest.Spec
