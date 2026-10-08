/-! A stream of order-book commands, three words each, and folds over its whole commands: a fold
over two chunks, the first of whole commands, is the fold over both, and a map that commutes with
each step commutes with the fold.  `Verify.lean` and the verified compiler's port of the order
book state their chunking theorems with these lemmas. -/

namespace Examples.Clob

/-- Command `l` of `commands`: its kind, price, and size. -/
def command (commands : Array UInt64) (l : UInt64) : UInt64 × UInt64 × UInt64 :=
  (commands[(3 * l).toNat]!, commands[(3 * l + 1).toNat]!, commands[(3 * l + 2).toNat]!)

/-- A fold of `step` over the whole commands of `commands`. -/
def foldCommands (step : UInt64 × UInt64 × UInt64 → σ → σ) (commands : Array UInt64)
    (x : σ) : σ :=
  Nat.fold (commands.size / 3) (fun i _ x => step (command commands (UInt64.ofNat i)) x) x

theorem command_append_left {c1 c2 : Array UInt64} {i : Nat} (hi : i < c1.size / 3)
    (hs : (c1 ++ c2).size < 2 ^ 62) :
    command (c1 ++ c2) (UInt64.ofNat i) = command c1 (UInt64.ofNat i) := by
  rw [Array.size_append] at hs
  have hj : ∀ j : Nat, j < 3 → (3 * UInt64.ofNat i + UInt64.ofNat j).toNat = 3 * i + j := by
    intro j hj
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hRead : ∀ j : Nat, j < 3 →
      (c1 ++ c2)[3 * i + j]! = c1[3 * i + j]! := fun j hj' => by
    rw [getElem!_pos (c1 ++ c2) _ (by simp; omega), getElem!_pos c1 _ (by omega),
      Array.getElem_append_left (by omega)]
  have h0 := hj 0 (by decide)
  have h1 := hj 1 (by decide)
  have h2 := hj 2 (by decide)
  simp only [UInt64.reduceOfNat, UInt64.add_zero, Nat.add_zero] at h0
  simp only [command] at *
  rw [show (3 * UInt64.ofNat i).toNat = 3 * i + 0 by simpa using h0,
    show (3 * UInt64.ofNat i + 1).toNat = 3 * i + 1 from h1,
    show (3 * UInt64.ofNat i + 2).toNat = 3 * i + 2 from h2,
    hRead 0 (by decide), hRead 1 (by decide), hRead 2 (by decide)]

theorem command_append_right {c1 c2 : Array UInt64} {i : Nat} (h3 : c1.size % 3 = 0)
    (hi : i < c2.size / 3) (hs : (c1 ++ c2).size < 2 ^ 62) :
    command (c1 ++ c2) (UInt64.ofNat (c1.size / 3 + i)) = command c2 (UInt64.ofNat i) := by
  rw [Array.size_append] at hs
  have hj : ∀ (a j : Nat), a < 2 ^ 61 → j < 3 →
      (3 * UInt64.ofNat a + UInt64.ofNat j).toNat = 3 * a + j := by
    intro a j ha hj
    simp only [UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_ofNat', UInt64.reduceToNat]
    omega
  have hRead : ∀ j : Nat, j < 3 →
      (c1 ++ c2)[3 * (c1.size / 3 + i) + j]! = c2[3 * i + j]! := fun j hj' => by
    rw [getElem!_pos (c1 ++ c2) _ (by simp; omega), getElem!_pos c2 _ (by omega),
      Array.getElem_append_right (by omega)]
    congr 1
    omega
  have h0 := hj (c1.size / 3 + i) 0 (by omega) (by decide)
  have h1 := hj (c1.size / 3 + i) 1 (by omega) (by decide)
  have h2 := hj (c1.size / 3 + i) 2 (by omega) (by decide)
  have g0 := hj i 0 (by omega) (by decide)
  have g1 := hj i 1 (by omega) (by decide)
  have g2 := hj i 2 (by omega) (by decide)
  simp only [UInt64.reduceOfNat, UInt64.add_zero, Nat.add_zero] at h0 g0
  simp only [command] at *
  rw [show (3 * UInt64.ofNat (c1.size / 3 + i)).toNat = 3 * (c1.size / 3 + i) + 0 by
      simpa using h0,
    show (3 * UInt64.ofNat (c1.size / 3 + i) + 1).toNat = 3 * (c1.size / 3 + i) + 1 from h1,
    show (3 * UInt64.ofNat (c1.size / 3 + i) + 2).toNat = 3 * (c1.size / 3 + i) + 2 from h2,
    show (3 * UInt64.ofNat i).toNat = 3 * i + 0 by simpa using g0,
    show (3 * UInt64.ofNat i + 1).toNat = 3 * i + 1 from g1,
    show (3 * UInt64.ofNat i + 2).toNat = 3 * i + 2 from g2,
    hRead 0 (by decide), hRead 1 (by decide), hRead 2 (by decide)]

/-- A fold over two chunks of commands, the first of whole commands, is the fold over both. -/
theorem foldCommands_append (step : UInt64 × UInt64 × UInt64 → σ → σ) (x : σ)
    {c1 c2 : Array UInt64} (h3 : c1.size % 3 = 0) (hs : (c1 ++ c2).size < 2 ^ 62) :
    foldCommands step c2 (foldCommands step c1 x) = foldCommands step (c1 ++ c2) x := by
  unfold foldCommands
  rw [Nat.fold_congr (show (c1 ++ c2).size / 3 = c1.size / 3 + c2.size / 3 by
    rw [Array.size_append]; omega), Nat.fold_add]
  congr 1
  · funext i hi y
    rw [command_append_right h3 hi hs]
  · exact Nat.fold_congr rfl _ _ |>.trans (by
      congr 1
      funext i hi y
      rw [command_append_left hi hs])

/-- A map that commutes with each step commutes with the fold. -/
theorem foldCommands_map {step : UInt64 × UInt64 × UInt64 → σ → σ}
    {step' : UInt64 × UInt64 × UInt64 → τ → τ} (π : σ → τ)
    (h : ∀ c x, π (step c x) = step' c (π x)) (cs : Array UInt64) (x : σ) :
    π (foldCommands step cs x) = foldCommands step' cs (π x) := by
  unfold foldCommands
  generalize cs.size / 3 = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [Nat.fold_succ, h, ih]

end Examples.Clob
