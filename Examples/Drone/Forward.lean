import Examples.Drone.Planner

/-! The forward pass: `validHeights` checks every height, and `forward` leaves a table whose
row `m` is the row of station `m` that `advance` builds from `initial`, for every station of the
terrain. -/

namespace Examples.Drone

open Examples.Drone Optimality Selection Costs Planner
open LeanExe.IR (loop_induction loop_congr build_size build_get)

namespace Forward

/-- `best` reads only the 45 choices from `base`, so it gives the same choice on any row that
holds them. -/
theorem best_congr (r0 r1 : UInt64) (table row : Array Choice) (base target sources : UInt64)
    (hsources : sources.toNat ≤ 45)
    (hrow : ∀ s : UInt64, s.toNat < 45 → table[(base + s).toNat]! = row[s.toNat]!) :
    best r0 r1 table base target sources = best r0 r1 row 0 target sources := by
  rw [best_loop, best_loop, loop_congr (g := bestStep r0 r1 row 0 target)]
  intro k hk s
  have hU : UInt64.size = 18446744073709551616 := rfl
  have hs : (UInt64.ofNat k).toNat < 45 := by
    rw [UInt64.toNat_ofNat_of_lt' (by omega)]; omega
  simp only [bestStep, hrow _ hs, UInt64.zero_add]

/-- The floor of station `k`. -/
def floors (terrain : Array UInt64) (k : Nat) : UInt64 := floorAt terrain (UInt64.ofNat k)

/-- Station `k` is the last of `count` stations. -/
def stops (count : UInt64) (k : Nat) : Bool := UInt64.ofNat k + 1 == count

/-- `table` holds the rows of the first `n` stations, 45 choices each. -/
def Rows (terrain : Array UInt64) (count : UInt64) (n : Nat) (table : Array Choice) : Prop :=
  table.size = 45 * n ∧ ∀ m, m < n → ∀ s : UInt64, s.toNat < 45 →
    table[45 * m + s.toNat]! = (layers (floors terrain) (stops count) m)[s.toNat]!

theorem rows_initial (terrain : Array UInt64) (count : UInt64) :
    Rows terrain count 1 initial := by
  refine ⟨by rw [initial_build, build_size]; rfl, fun m hm s _ => ?_⟩
  obtain rfl : m = 0 := by omega
  simp [layers]

theorem choice_eta (c : Choice) : (⟨c.time, c.excess, c.parent⟩ : Choice) = c := rfl

/-- Below `count`, `extend` adds the row of station `i`. -/
theorem extend_rows (terrain : Array UInt64) (count i : UInt64) (table : Array Choice)
    (hi : 1 ≤ i.toNat) (hlt : i < count) (hcount : count.toNat ≤ 64)
    (hrows : Rows terrain count i.toNat table) :
    ∃ table', extend terrain count i table = (0, i + 1, table') ∧
      Rows terrain count (i.toNat + 1) table' := by
  obtain ⟨hsize, hrow⟩ := hrows
  have hU : UInt64.size = 18446744073709551616 := rfl
  have hS : stateCount.toNat = 45 := rfl
  have hltN := UInt64.lt_iff_toNat_lt.mp hlt
  have hsizeU : table.size.toUInt64.toNat = 45 * i.toNat := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' (by omega), hsize]
  have hcountU : (table.size.toUInt64 + stateCount).toNat = 45 * i.toNat + 45 := by
    rw [UInt64.toNat_add, hsizeU, hS]; exact Nat.mod_eq_of_lt (by omega)
  have hbase : (table.size.toUInt64 - stateCount).toNat = 45 * (i.toNat - 1) := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hsizeU, hS]; omega)),
      hsizeU, hS]
    omega
  have hprev : (UInt64.ofNat (i.toNat - 1)) = i - 1 := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_ofNat_of_lt' (by omega), UInt64.toNat_sub_of_le _ _
      (UInt64.le_iff_toNat_le.mpr (by simp; omega))]
    simp
  refine ⟨?w, ?heq, ?hs, ?hr⟩
  case heq =>
    simp only [extend, hlt, ite_true]
    rfl
  case hs => rw [build_size, hcountU]; omega
  case hr =>
    intro m hm s hs
    rw [build_get (by rw [hcountU]; omega)]
    by_cases hmi : m < i.toNat
    · have hj : UInt64.ofNat (45 * m + s.toNat) < table.size.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hsizeU, UInt64.toNat_ofNat_of_lt' (by omega)]; omega
      have hjN : (UInt64.ofNat (45 * m + s.toNat)).toNat = 45 * m + s.toNat :=
        UInt64.toNat_ofNat_of_lt' (by omega)
      simp only [hj, decide_true, Bool.true_or, ite_true, hjN]
      rw [choice_eta]
      exact hrow m hmi s hs
    · obtain rfl : m = i.toNat := by omega
      have hj : ¬UInt64.ofNat (45 * i.toNat + s.toNat) < table.size.toUInt64 := by
        rw [UInt64.lt_iff_toNat_lt, hsizeU, UInt64.toNat_ofNat_of_lt' (by omega)]; omega
      have htarget : UInt64.ofNat (45 * i.toNat + s.toNat) - table.size.toUInt64 = s := by
        apply UInt64.toNat_inj.mp
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by
          rw [hsizeU, UInt64.toNat_ofNat_of_lt' (by omega)]; omega)),
          UInt64.toNat_ofNat_of_lt' (by omega), hsizeU]
        omega
      simp only [hj, decide_false, Bool.false_or, ite_false, htarget]
      rw [choice_eta]
      obtain ⟨k, hk⟩ : ∃ k, i.toNat = k + 1 := ⟨i.toNat - 1, by omega⟩
      rw [hk]
      have hiK : UInt64.ofNat (k + 1) = i := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_ofNat_of_lt' (by omega)]; omega
      have hsources : (if (i + 1 == count && s != 0) = true then (0 : UInt64) else stateCount) =
          sourceCount (stops count (k + 1)) s := by
        simp only [sourceCount, stops, hiK]
        by_cases h1 : i + 1 = count <;> by_cases h2 : s = 0 <;> simp [h1, h2, stateCount]
      rw [hsources, best_congr _ _ table (layers (floors terrain) (stops count) k) _ s _
        (Costs.sourceCount_le _ _) fun s' hs' => by
          rw [show (table.size.toUInt64 - stateCount + s').toNat = 45 * k + s'.toNat by
            rw [UInt64.toNat_add, hbase, Nat.mod_eq_of_lt (by omega)]; omega]
          exact hrow k (by omega) s' hs']
      simp only [layers]
      rw [advance_get _ _ _ _ _ _ hs]
      congr 1
      · simp only [floors]; rw [← hprev, hk, Nat.add_sub_cancel]
      · simp only [floors, hiK]

/-- From station `i` with the rows below it, the loop of `forward` ends with status 1 at
station `max count 1` and the rows of every station below it. -/
theorem go_rows (terrain : Array UInt64) (count : UInt64) (hcount : count.toNat ≤ 64) :
    ∀ (f : Nat) (i : UInt64) (table : Array Choice), 1 ≤ i.toNat →
      i.toNat ≤ max count.toNat 1 → max count.toNat 1 + 1 ≤ i.toNat + f →
      Rows terrain count i.toNat table →
      ∃ table', LeanExe.repeatWhile.go (fun (s : UInt64 × UInt64 × Array Choice) => s.1 == 0)
          (fun s => extend terrain count s.2.1 s.2.2) f ((0 : UInt64), i, table) =
          ((1 : UInt64), UInt64.ofNat (max count.toNat 1), table') ∧
        Rows terrain count (max count.toNat 1) table' := by
  intro f
  induction f with
  | zero => intro i table _ hi hf _; omega
  | succ f ih =>
    intro i table h1 hi hf hrows
    simp only [LeanExe.repeatWhile.go, beq_self_eq_true, ite_true]
    by_cases hlt : i < count
    · obtain ⟨table', hext, hrows'⟩ := extend_rows terrain count i table h1 hlt hcount hrows
      have hltN := UInt64.lt_iff_toNat_lt.mp hlt
      have hiN : (i + 1).toNat = i.toNat + 1 := by
        rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt (by simp; omega)
      rw [hext]
      exact ih (i + 1) table' (by omega) (by omega) (by omega) (by rw [hiN]; exact hrows')
    · have hext : extend terrain count i table = (1, i, table) := by
        simp only [extend, hlt, ite_false]
      have hge : count.toNat ≤ i.toNat := by
        rw [UInt64.lt_iff_toNat_lt] at hlt; omega
      have hmax : max count.toNat 1 = i.toNat := by omega
      rw [hext]
      refine ⟨table, ?_, by rw [hmax]; exact hrows⟩
      cases f <;> simp [LeanExe.repeatWhile.go, hmax]

/-- `forward` ends with status 1 and the rows of all `max count 1` stations. -/
theorem forward_rows (terrain : Array UInt64) (count : UInt64) (hcount : count.toNat ≤ 64) :
    ∃ table, forward terrain count =
        ((1 : UInt64), UInt64.ofNat (max count.toNat 1), table) ∧
      Rows terrain count (max count.toNat 1) table :=
  go_rows terrain count hcount 64 1 initial (by decide) (by simp) (by simp; omega)
    (rows_initial terrain count)

/-- `validHeights` holds exactly when every height is at most 1,000,000. -/
theorem validHeights_iff (terrain : Array UInt64) (hlen : terrain.size < 2 ^ 64) :
    validHeights terrain = true ↔ ∀ k, k < terrain.size → terrain[k]! ≤ 1000000 := by
  have hb := UInt64.toNat_lt_size terrain.size.toUInt64
  have hU : UInt64.size = 18446744073709551616 := rfl
  have h := loop_induction (n := terrain.size.toUInt64) (init := true)
    (f := fun i ok => ok && decide (terrain[i.toNat]! ≤ 1000000))
    (fun k ok => (ok = true ↔ ∀ j, j < k → terrain[j]! ≤ 1000000))
    (by simp) fun k ok hk hok => by
      have hkN : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by omega)
      simp only [Bool.and_eq_true, decide_eq_true_eq, hok, hkN]
      constructor
      · rintro ⟨hall, hlast⟩ j hj
        by_cases hjk : j = k
        · subst hjk; exact hlast
        · exact hall j (by omega)
      · intro hall
        exact ⟨fun j hj => hall j (by omega), hall k (by omega)⟩
  have hsize : terrain.size.toUInt64.toNat = terrain.size := by
    rw [Nat.toUInt64, UInt64.toNat_ofNat_of_lt' hlen]
  rw [hsize] at h
  exact h

end Forward

end Examples.Drone
