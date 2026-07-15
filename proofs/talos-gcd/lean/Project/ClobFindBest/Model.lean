import Project.Clob

/-!
# Source model for `findBest`

These definitions restate the CLOB search over the proof workspace's shared
order representation.  They preserve `UInt64` comparisons and first-index
tie breaking.
-/

namespace Project.ClobFindBest.Model

open Project.Clob

def oppositeSideL (side : UInt64) : UInt64 :=
  if side = 0 then 1 else 0

abbrev crossesL (taker maker : OrderL) : Prop :=
  if taker.oside = 0 then maker.oprice ≤ taker.oprice
  else taker.oprice ≤ maker.oprice

abbrev eligibleL (taker maker : OrderL) : Prop :=
  maker.oside = oppositeSideL taker.oside ∧
  maker.otrader ≠ taker.otrader ∧
  crossesL taker maker

abbrev betterPriceL (taker candidate incumbent : OrderL) : Prop :=
  if taker.oside = 0 then candidate.oprice < incumbent.oprice
  else incumbent.oprice < candidate.oprice

def bestStepL (os : List OrderL) (taker : OrderL) (i : Nat) :
    Option Nat → Option Nat
  | none => if eligibleL taker os[i]! then some i else none
  | some j =>
      if eligibleL taker os[i]! ∧ betterPriceL taker os[i]! os[j]! then
        some i
      else
        some j

def bestPrefixL (os : List OrderL) (taker : OrderL) : Nat → Option Nat
  | 0 => none
  | k + 1 => bestStepL os taker k (bestPrefixL os taker k)

def findBestFuelL : Nat → List OrderL → OrderL → Nat → Option Nat → Option Nat
  | 0, _, _, _, best => best
  | fuel + 1, os, taker, i, best =>
      if i < os.length then
        let candidate := os[i]!
        let best' :=
          match best with
          | none => if eligibleL taker candidate then some i else none
          | some j =>
              if eligibleL taker candidate ∧
                  betterPriceL taker candidate os[j]! then
                some i
              else
                some j
        findBestFuelL fuel os taker (i + 1) best'
      else
        best

def findBestL (os : List OrderL) (taker : OrderL) : Option Nat :=
  findBestFuelL (os.length + 1) os taker 0 none

theorem findBestFuelL_from_prefix (os : List OrderL) (taker : OrderL)
    (k : Nat) (hk : k ≤ os.length) :
    findBestFuelL (os.length + 1 - k) os taker k
        (bestPrefixL os taker k) =
      bestPrefixL os taker os.length := by
  induction hrem : os.length - k using Nat.strong_induction_on generalizing k with
  | h n ih =>
      by_cases hkend : k = os.length
      · subst k
        simp [findBestFuelL]
      · have hklt : k < os.length := Nat.lt_of_le_of_ne hk hkend
        have hfuel : os.length + 1 - k = (os.length - k) + 1 := by omega
        rw [hfuel, findBestFuelL, if_pos hklt]
        change findBestFuelL (os.length - k) os taker (k + 1)
            (bestPrefixL os taker (k + 1)) =
          bestPrefixL os taker os.length
        have hnextfuel : os.length - k = os.length + 1 - (k + 1) := by
          omega
        rw [hnextfuel]
        exact ih (os.length - (k + 1)) (by omega) (k + 1) (by omega) rfl

theorem findBestL_eq_prefix (os : List OrderL) (taker : OrderL) :
    findBestL os taker = bestPrefixL os taker os.length := by
  unfold findBestL
  simpa [bestPrefixL] using findBestFuelL_from_prefix os taker 0 (Nat.zero_le _)

theorem bestPrefixL_some_lt (os : List OrderL) (taker : OrderL)
    (k j : Nat) (h : bestPrefixL os taker k = some j) : j < k := by
  induction k with
  | zero => simp [bestPrefixL] at h
  | succ k ih =>
      have hchoice : j = k ∨ bestPrefixL os taker k = some j := by
        simp only [bestPrefixL] at h
        unfold bestStepL at h
        split at h <;> split at h <;> simp_all
      rcases hchoice with rfl | hprev
      · omega
      · exact Nat.lt_succ_of_lt (ih hprev)

theorem findBestL_some_lt (os : List OrderL) (taker : OrderL)
    (j : Nat) (h : findBestL os taker = some j) : j < os.length := by
  rw [findBestL_eq_prefix] at h
  exact bestPrefixL_some_lt os taker os.length j h

def optionTag : Option Nat → UInt64
  | none => 0
  | some _ => 1

def optionPayload : Option Nat → UInt64
  | none => 0
  | some i => UInt64.ofNat i

def optionVals (value : Option Nat) : List Wasm.Value :=
  [.i64 (optionPayload value), .i64 (optionTag value)]

end Project.ClobFindBest.Model
