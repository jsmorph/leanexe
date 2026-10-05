import Project.Drone.Output

/-! `compute` returns the flight that attains the least cost: for valid terrain its words are the
altitude and speed of each station on an admitted flight from rest on the ground to rest on the
ground, and no admitted flight costs less. -/

namespace Project.Drone.Output

open LeanExe.Examples.Drone Arithmetic Optimality Selection Costs Planner Forward
open Project.IR (loop_induction build_size build_get)

/-- The inner loop of `output` follows the parents back from the stopped state of the last
station to station `k`. -/
theorem output_state (terrain : Array UInt64) (count : UInt64) (table : Array Choice)
    (h1 : 1 ≤ count.toNat) (h64 : count.toNat ≤ 64) (hrows : Rows terrain count count.toNat table)
    (k : Nat) (hk : k < count.toNat) :
    LeanExe.loop (count - 1 - UInt64.ofNat k) (0 : UInt64)
        (fun j s => table[((count - 1 - j) * stateCount + s).toNat]!.parent) =
      chain (floors terrain) (stops count) (count.toNat - 1) 0 (count.toNat - 1 - k) := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  have hkN : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by omega)
  have hc1 : (count - 1).toNat = count.toNat - 1 := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega))]; simp
  have hn : (count - 1 - UInt64.ofNat k).toNat = count.toNat - 1 - k := by
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hc1, hkN]; omega)), hc1,
      hkN]
  have h := loop_induction (n := count - 1 - UInt64.ofNat k) (init := (0 : UInt64))
    (f := fun j s => table[((count - 1 - j) * stateCount + s).toNat]!.parent)
    (fun j s => s = chain (floors terrain) (stops count) (count.toNat - 1) 0 j ∧ s.toNat < 45)
    ⟨rfl, by decide⟩ fun j s hj ⟨hs, hs45⟩ => by
      rw [hn] at hj
      have hjN : (UInt64.ofNat j).toNat = j := UInt64.toNat_ofNat_of_lt' (by omega)
      have hm : (count - 1 - UInt64.ofNat j).toNat = count.toNat - 1 - j := by
        rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by rw [hc1, hjN]; omega)),
          hc1, hjN]
      have hidx : ((count - 1 - UInt64.ofNat j) * stateCount + s).toNat =
          45 * (count.toNat - 1 - j) + s.toNat := by
        have h45 : stateCount.toNat = 45 := rfl
        have ha : (count.toNat - 1 - j) * 45 < 2 ^ 64 := by omega
        have hb : (count.toNat - 1 - j) * 45 + s.toNat < 2 ^ 64 := by omega
        rw [UInt64.toNat_add, UInt64.toNat_mul, hm, h45, Nat.mod_eq_of_lt ha,
          Nat.mod_eq_of_lt hb]
        omega
      have hrow := hrows.2 (count.toNat - 1 - j) (by omega) s hs45
      rw [hidx, hrow, chain_last, ← hs]
      exact ⟨rfl, layers_parent _ _ _ s hs45⟩
  rw [hn] at h
  exact h.1

theorem output_size (terrain : Array UInt64) (count : UInt64) (table : Array Choice)
    (h64 : count.toNat ≤ 64) : (output terrain table count).size = 2 * count.toNat := by
  simp only [output, build_size]
  rw [UInt64.toNat_mul]
  exact Nat.mod_eq_of_lt (by simp; omega)

/-- `output` returns the words of the flight that ends in the stopped state of the last
station. -/
theorem output_toList (terrain : Array UInt64) (count : UInt64) (table : Array Choice)
    (h1 : 1 ≤ count.toNat) (h64 : count.toNat ≤ 64) (hrows : Rows terrain count count.toNat table) :
    (output terrain table count).toList =
      words (floors terrain) (stops count) (count.toNat - 1) 0 := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  apply List.ext_getElem
  · rw [Array.length_toList, output_size _ _ _ h64, words_length]; omega
  · intro e he _
    rw [Array.length_toList, output_size _ _ _ h64] at he
    rw [Array.getElem_toList, ← getElem!_pos _ _ (by rw [output_size _ _ _ h64]; omega)]
    simp only [output]
    rw [build_get (by rw [UInt64.toNat_mul]; rw [Nat.mod_eq_of_lt (by simp; omega)]; simpa)]
    have heN : (UInt64.ofNat e).toNat = e := UInt64.toNat_ofNat_of_lt' (by omega)
    have hk : UInt64.ofNat e / 2 = UInt64.ofNat (e / 2) := by
      apply UInt64.toNat_inj.mp
      rw [UInt64.toNat_div, heN, UInt64.toNat_ofNat_of_lt' (by omega)]; rfl
    have hstate := output_state terrain count table h1 h64 hrows (e / 2) (by omega)
    rw [← getElem!_pos _ _ (by rw [words_length]; omega)]
    simp only [hk, hstate]
    rcases Nat.even_or_odd e with ⟨m, rfl⟩ | ⟨m, rfl⟩
    · have hm : (m + m) / 2 = m := by omega
      have hmod : UInt64.ofNat (m + m) % 2 = 0 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' (by omega)]
        simp; omega
      have hw' := (words_get (floors terrain) (stops count) (count.toNat - 1) 0 m (by omega)).1
      simp only [hm, hmod, beq_self_eq_true, ite_true]
      rw [show m + m = 2 * m by omega, hw']
      rfl
    · have hm : (2 * m + 1) / 2 = m := by omega
      have hmod : UInt64.ofNat (2 * m + 1) % 2 = 1 := by
        apply UInt64.toNat_inj.mp; rw [UInt64.toNat_mod, UInt64.toNat_ofNat_of_lt' (by omega)]
        simp
      have hw' := (words_get (floors terrain) (stops count) (count.toNat - 1) 0 m (by omega)).2
      simp only [hm, hmod]
      have h10 : ((1 : UInt64) == 0) = false := rfl
      rw [h10, hw']
      rfl

/-- Terrain the planner accepts: at most 64 heights, each at most 1,000,000. -/
def terrainBound (terrain : Array UInt64) : Prop :=
  terrain.size ≤ 64 ∧ ∀ i, i < terrain.size → terrain[i]!.toNat ≤ 1000000

theorem floors_nat (terrain : Array UInt64) (h : terrainBound terrain) (k : Nat)
    (hk : k < terrain.size) :
    (floors terrain k).toNat =
      terrain[k]!.toNat + if k = 0 ∨ k + 1 = terrain.size then 0 else 100 := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  have ht := h.2 k hk
  have h64 := h.1
  have hkN : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by omega)
  have hiff : (UInt64.ofNat k = 0 ∨ UInt64.ofNat k + 1 = UInt64.ofNat terrain.size) ↔
      (k = 0 ∨ k + 1 = terrain.size) := by
    constructor
    · rintro (h0 | h1)
      · left; have := congrArg UInt64.toNat h0; rw [hkN] at this; simpa using this
      · right
        have := congrArg UInt64.toNat h1
        rw [UInt64.toNat_add, hkN, UInt64.toNat_ofNat_of_lt' (by omega), UInt64.toNat_one] at this
        omega
    · rintro (h0 | h1)
      · left; subst h0; rfl
      · right; rw [← h1]; simp
  simp only [floors, floorAt, Nat.toUInt64_eq, hkN, Bool.or_eq_true, beq_iff_eq]
  by_cases hc : k = 0 ∨ k + 1 = terrain.size
  · rw [if_pos (hiff.mpr hc), if_pos hc, UInt64.toNat_add]
    simp
  · rw [if_neg (fun h' => hc (hiff.mp h')), if_neg hc, UInt64.toNat_add]
    simp; omega

theorem floors_bound (terrain : Array UInt64) (h : terrainBound terrain) (k : Nat)
    (hk : k < terrain.size) : (floors terrain k).toNat ≤ 1000100 := by
  rw [floors_nat terrain h k hk]
  have := h.2 k hk
  split <;> omega

/-- For valid terrain, `compute` returns the words of the flight that ends at rest at the last
station. -/
theorem compute_valid (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    (compute terrain).toList =
      words (floors terrain) (stops terrain.size.toUInt64) (terrain.size - 1) 0 := by
  have hU : UInt64.size = 18446744073709551616 := rfl
  have h64 := h.1
  have hsz : terrain.size.toUInt64.toNat = terrain.size := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by omega)]
  have hvalid : validHeights terrain = true :=
    (validHeights_iff terrain (by omega)).mpr fun k hk =>
      UInt64.le_iff_toNat_le.mpr (by have := h.2 k hk; simpa using this)
  have hpos : 0 < terrain.size.toUInt64 := UInt64.lt_iff_toNat_lt.mpr (by rw [hsz]; simpa)
  have hle : terrain.size.toUInt64 ≤ 64 := UInt64.le_iff_toNat_le.mpr (by rw [hsz]; simpa)
  obtain ⟨table, hfwd, hrows⟩ := forward_rows terrain terrain.size.toUInt64 (by omega)
  have hmax : max terrain.size.toUInt64.toNat 1 = terrain.size.toUInt64.toNat := by omega
  rw [hmax] at hrows hfwd
  simp only [compute, hvalid, hpos, hle, decide_true, Bool.and_self, ite_true, hfwd]
  rw [output_toList terrain _ table (by omega) (by omega) hrows, hsz]

/-- For valid terrain, `compute` returns the words of an admitted flight from rest on the ground
at the first station to rest on the ground at the last, whose cost is the label of that state,
and no admitted flight to it costs less. -/
theorem compute_correct (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    let r := floors terrain
    let stop := stops terrain.size.toUInt64
    let n := terrain.size - 1
    (compute terrain).size = 2 * terrain.size ∧
    Encoded r stop n 0 (rowCost (layers r stop n) 0) (compute terrain).toList ∧
    ∀ other, Flight r stop n 0 other → (rowCost (layers r stop n) 0).LE other := by
  intro r stop n
  have h64 := h.1
  have hr : ∀ j, j ≤ n → (r j).toNat ≤ 1000100 := fun j hj =>
    floors_bound terrain h j (by omega)
  have henc := words_encoded r stop n 0 (by omega) hr (by decide)
    (terminal_finite r stop n (by omega) hr)
  rw [← compute_valid terrain h hn] at henc
  refine ⟨?_, henc, (terminal_optimal r stop n (by omega) hr).2⟩
  have hlen := henc.length
  simp only [Array.length_toList] at hlen
  omega

/-- `compute` returns `#[]` for empty terrain and for terrain the planner does not accept. -/
theorem compute_invalid (terrain : Array UInt64) (hsize : terrain.size < 2 ^ 64)
    (h : ¬(terrainBound terrain ∧ 0 < terrain.size)) : compute terrain = #[] := by
  have hsz : terrain.size.toUInt64.toNat = terrain.size := by
    rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hsize]
  have hcount : (if (decide (0 < terrain.size.toUInt64) && decide (terrain.size.toUInt64 ≤ 64) &&
      validHeights terrain) = true then terrain.size.toUInt64 else 0) = 0 := by
    rw [if_neg]
    intro hc
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨hpos, hle⟩, hvalid⟩ := hc
    rw [UInt64.lt_iff_toNat_lt, hsz] at hpos
    rw [UInt64.le_iff_toNat_le, hsz] at hle
    refine h ⟨⟨by simpa using hle, fun k hk => ?_⟩, by simpa using hpos⟩
    have := (validHeights_iff terrain hsize).mp hvalid k hk
    simpa [UInt64.le_iff_toNat_le] using this
  obtain ⟨table, hfwd, -⟩ := forward_rows terrain 0 (by decide)
  simp only [compute, hcount, hfwd]
  simp [output, LeanExe.build]

theorem Encoded.first_pair {r stop n state c output} (encoded : Encoded r stop n state c output) :
    output.take 2 = [r 0, 0] := by
  induction encoded with
  | start => rfl
  | step previous _ _ _ ih =>
    rw [List.take_append_of_le_length (by rw [previous.length]; omega)]
    exact ih

theorem Encoded.last_pair {r stop n state c output} (encoded : Encoded r stop n state c output) :
    output.drop (2 * n) = [altitude (r n) state, speed state] := by
  cases encoded with
  | start => simp [altitude, speed]
  | @step i source target c out previous _ _ _ =>
    rw [← previous.length, List.drop_left]

/-- For valid terrain, `compute` starts and ends on the terrain at rest. -/
theorem compute_endpoints (terrain : Array UInt64) (h : terrainBound terrain)
    (hn : 0 < terrain.size) :
    (compute terrain).toList.take 2 = [terrain[0]!, 0] ∧
    (compute terrain).toList.drop (2 * (terrain.size - 1)) = [terrain[terrain.size - 1]!, 0] := by
  have he := (compute_correct terrain h hn).2.1
  have h0 := floors_nat terrain h 0 hn
  have hl := floors_nat terrain h (terrain.size - 1) (by omega)
  refine ⟨?_, ?_⟩
  · rw [he.first_pair]
    congr 1
    apply UInt64.toNat_inj.mp
    rw [h0]; simp
  · rw [he.last_pair]
    simp only [altitude, speed]
    congr 1
    apply UInt64.toNat_inj.mp
    have : (UInt64.ofNat 0 / 5 * 25 : UInt64) = 0 := rfl
    simp only [UInt64.toNat_add]
    rw [hl, if_pos (Or.inr (by omega))]
    simp

end Project.Drone.Output
