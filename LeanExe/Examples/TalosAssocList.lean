namespace LeanExe
namespace Examples.TalosAssocList

def lookup : List (UInt64 × UInt64) → UInt64 → UInt64
  | [], _ => 0
  | (k, v) :: rest, key =>
      if k == key then
        v
      else
        lookup rest key

def sample : List (UInt64 × UInt64) :=
  [(7, 70), (2, 20), (9, 90), (2, 22)]

def lookupDemo (key : UInt64) : UInt64 :=
  lookup sample key

def lookupDemoExpected (key : UInt64) : UInt64 :=
  if key == 7 then
    70
  else if key == 2 then
    20
  else if key == 9 then
    90
  else
    0

def LookupSpec (runsTo : UInt64 → UInt64 → Prop) : Prop :=
  ∀ key, runsTo key (lookupDemoExpected key)

def leanRunsTo (key output : UInt64) : Prop :=
  lookupDemo key = output

theorem lookupDemo_eq_expected (key : UInt64) :
    lookupDemo key = lookupDemoExpected key := by
  unfold lookupDemo sample lookupDemoExpected
  simp [lookup]
  by_cases h7 : key = 7
  · subst key
    simp
  · by_cases h2 : key = 2
    · subst key
      simp
    · by_cases h9 : key = 9
      · subst key
        simp
      · have h7' : (7 : UInt64) ≠ key := fun h => h7 h.symm
        have h2' : (2 : UInt64) ≠ key := fun h => h2 h.symm
        have h9' : (9 : UInt64) ≠ key := fun h => h9 h.symm
        simp [h7, h2, h9, h7', h2', h9']

theorem lookupDemo_correct : LookupSpec leanRunsTo := by
  intro key
  exact lookupDemo_eq_expected key

end Examples.TalosAssocList
end LeanExe
