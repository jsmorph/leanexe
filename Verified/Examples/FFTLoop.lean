import Verified.Examples.FFTBits
import Verified.Examples.FFTIndex
import Verified.Examples.FourierLoop
import Verified.Examples.FourierPowerEmbedding
import Verified.Examples.FourierInverseLoop

namespace Verified.Examples.FFTLoop

def copyReversed (n p : UInt64) (xs : Array Float) : Array Float :=
  FFT.copyReversed p n xs

def stageWith (n width : UInt64) (w : Array (Float × Float)) (dir : Float)
    (ys : Array Float) : Array Float :=
  FFT.stageWith w dir n width ys

def entries (ys : Array Float) (lo hi : Nat) : (Float × Float) × (Float × Float) :=
  ((ys[2 * lo]!, ys[2 * lo + 1]!), (ys[2 * hi]!, ys[2 * hi + 1]!))

def butterflyValues (inputs : (Float × Float) × (Float × Float)) (c d : Float) :
    (Float × Float) × (Float × Float) :=
  let tr := inputs.2.1 * c - inputs.2.2 * d
  let ti := inputs.2.1 * d + inputs.2.2 * c
  ((inputs.1.1 + tr, inputs.1.2 + ti), (inputs.1.1 - tr, inputs.1.2 - ti))

def butterfly (ys : Array Float) (lo hi : Nat) (c d : Float) : Array Float :=
  let out := butterflyValues (entries ys lo hi) c d
  (((ys.set! (2 * lo) out.1.1).set! (2 * lo + 1) out.1.2).set!
    (2 * hi) out.2.1).set! (2 * hi + 1) out.2.2

theorem butterfly_size (ys : Array Float) (lo hi : Nat) (c d : Float) :
    (butterfly ys lo hi c d).size = ys.size := by
  simp only [butterfly, Array.size_set!]

theorem butterfly_entries (ys : Array Float) (lo hi : Nat) (c d : Float)
    (hlo : lo < hi) (hhi : 2 * hi + 1 < ys.size) :
    entries (butterfly ys lo hi c d) lo hi = butterflyValues (entries ys lo hi) c d := by
  unfold butterfly entries
  dsimp only
  apply Prod.ext
  · apply Prod.ext
    · dsimp only
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_self _ _ _ (by omega)]
    · dsimp only
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_self _ _ _ (by simp only [Array.size_set!]; omega)]
  · apply Prod.ext
    · dsimp only
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
        Array.getElem!_set!_self _ _ _ (by simp only [Array.size_set!]; omega)]
    · dsimp only
      rw [Array.getElem!_set!_self _ _ _ (by simp only [Array.size_set!]; omega)]

theorem butterfly_get_unchanged (ys : Array Float) (lo hi k : Nat) (c d : Float)
    (hk0 : k ≠ 2 * lo) (hk1 : k ≠ 2 * lo + 1)
    (hk2 : k ≠ 2 * hi) (hk3 : k ≠ 2 * hi + 1) :
    (butterfly ys lo hi c d)[k]! = ys[k]! := by
  unfold butterfly
  rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
    Array.getElem!_set!_ne _ _ _ _ (by omega),
    Array.getElem!_set!_ne _ _ _ _ (by omega),
    Array.getElem!_set!_ne _ _ _ _ (by omega)]

theorem butterfly_other_entries (ys : Array Float) (h i j : Nat) (c d : Float)
    (hh : 0 < h) (hij : i ≠ j) :
    entries (butterfly ys (FFTIndex.lower h i) (FFTIndex.upper h i) c d)
        (FFTIndex.lower h j) (FFTIndex.upper h j) =
      entries ys (FFTIndex.lower h j) (FFTIndex.upper h j) := by
  obtain ⟨h00, h01, h10, h11⟩ := FFTIndex.disjoint h i j hh hij
  unfold entries
  rw [butterfly_get_unchanged _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega),
    butterfly_get_unchanged _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega),
    butterfly_get_unchanged _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega),
    butterfly_get_unchanged _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega)]

def wordEntries (ys : Array Float) (lo hi : UInt64) : (Float × Float) × (Float × Float) :=
  ((ys[(2 * lo).toNat]!, ys[(2 * lo + 1).toNat]!),
    (ys[(2 * hi).toNat]!, ys[(2 * hi + 1).toNat]!))

def wordButterfly (ys : Array Float) (lo hi : UInt64) (c d : Float) : Array Float :=
  let out := butterflyValues (wordEntries ys lo hi) c d
  (((ys.set! (2 * lo).toNat out.1.1).set! (2 * lo + 1).toNat out.1.2).set!
    (2 * hi).toNat out.2.1).set! (2 * hi + 1).toNat out.2.2

theorem wordButterfly_eq (ys : Array Float) (n lo hi : UInt64) (c d : Float)
    (hn : n.toNat ≤ 2 ^ 32) (hlo : lo < n) (hhi : hi < n) :
    wordButterfly ys lo hi c d = butterfly ys lo.toNat hi.toNat c d := by
  unfold wordButterfly wordEntries butterfly entries
  rw [FourierLoop.twice_toNat n lo hn hlo, FourierLoop.twice_add_one_toNat n lo hn hlo,
    FourierLoop.twice_toNat n hi hn hhi, FourierLoop.twice_add_one_toNat n hi hn hhi]

def stageNat (h blocks : Nat) (w : Array (Float × Float)) (dir : Float)
    (ys : Array Float) : Array Float :=
  Nat.fold (h * blocks) (fun i _ acc =>
    let t := w[(i % h) * blocks]!
    butterfly acc (FFTIndex.lower h i) (FFTIndex.upper h i) t.1 (dir * t.2)) ys

theorem stageNat_entries (h blocks : Nat) (w : Array (Float × Float)) (dir : Float)
    (ys : Array Float) (hh : 0 < h) (hsize : ys.size = 4 * h * blocks)
    (i : Nat) (hi : i < h * blocks) :
    entries (stageNat h blocks w dir ys) (FFTIndex.lower h i) (FFTIndex.upper h i) =
      butterflyValues (entries ys (FFTIndex.lower h i) (FFTIndex.upper h i))
        w[(i % h) * blocks]!.1 (dir * w[(i % h) * blocks]!.2) := by
  let P (m : Nat) (acc : Array Float) : Prop :=
    acc.size = ys.size ∧ ∀ j, j < h * blocks →
      entries acc (FFTIndex.lower h j) (FFTIndex.upper h j) =
        if j < m then
          butterflyValues (entries ys (FFTIndex.lower h j) (FFTIndex.upper h j))
            w[(j % h) * blocks]!.1 (dir * w[(j % h) * blocks]!.2)
        else entries ys (FFTIndex.lower h j) (FFTIndex.upper h j)
  have hstate : ∀ m, m ≤ h * blocks → P m (Nat.fold m (fun j _ acc =>
      let t := w[(j % h) * blocks]!
      butterfly acc (FFTIndex.lower h j) (FFTIndex.upper h j) t.1 (dir * t.2)) ys) := by
    intro m
    induction m with
    | zero => intro _; exact ⟨rfl, by intro j _; simp⟩
    | succ m ih =>
      intro hm
      have hprev := ih (by omega)
      have hmlt : m < h * blocks := by omega
      rw [Nat.fold_succ]
      refine ⟨by rw [butterfly_size]; exact hprev.1, ?_⟩
      intro j hj
      by_cases hjm : j = m
      · subst j
        have hfuture := hprev.2 m hmlt
        rw [ite_eq_right (by omega : ¬m < m)] at hfuture
        rw [butterfly_entries _ _ _ _ _ (FFTIndex.lower_lt_upper h m hh) (by
          rw [hprev.1, hsize]
          have hupper := FFTIndex.upper_lt h blocks m hh hmlt
          nlinarith only [hupper]), hfuture, ite_eq_left (by omega : m < m + 1)]
      · rw [butterfly_other_entries _ h m j _ _ hh (Ne.symm hjm)]
        have hlt : (j < m) = (j < m + 1) := propext (by omega)
        simpa only [hlt] using hprev.2 j hj
  have hfinal := (hstate (h * blocks) le_rfl).2 i hi
  simpa only [ite_eq_left hi, stageNat] using hfinal

theorem stageWith_eq_stageNat (n width : UInt64) (w : Array (Float × Float)) (dir : Float)
    (ys : Array Float) (h blocks : Nat) (hh : 0 < h)
    (hn : n.toNat = 2 * h * blocks) (hwidth : width.toNat = 2 * h)
    (hnmax : n.toNat ≤ 2 ^ 32) : stageWith n width w dir ys = stageNat h blocks w dir ys := by
  have hn2 : (n / 2).toNat = h * blocks := by
    rw [UInt64.toNat_div, hn]
    simp only [UInt64.reduceToNat]
    rw [Nat.mul_assoc]
    exact Nat.mul_div_cancel_left _ (by omega)
  unfold stageWith FFT.stageWith LeanExe.loop stageNat
  dsimp only
  rw [hn2]
  congr 1
  funext i hi acc
  have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by
    have hle : h * blocks ≤ n.toNat := by rw [hn]; nlinarith only [Nat.zero_le (h * blocks)]
    exact ((hi.trans_le hle).trans_le hnmax).trans (by norm_num [UInt64.size]))
  have hw := FFTIndex.word_indices n width (UInt64.ofNat i) h blocks hh hn hwidth hnmax
    (by rw [hi64]; exact hi)
  have hlo : FFTIndex.lowerWord width (UInt64.ofNat i) < n := UInt64.lt_iff_toNat_lt.mpr (by
    rw [hw.1, hi64, hn]
    exact FFTIndex.lower_lt h blocks i hh hi)
  have hhi : FFTIndex.upperWord width (UInt64.ofNat i) < n := UInt64.lt_iff_toNat_lt.mpr (by
    rw [hw.2.1, hi64, hn]
    exact FFTIndex.upper_lt h blocks i hh hi)
  change wordButterfly acc (FFTIndex.lowerWord width (UInt64.ofNat i))
      (FFTIndex.upperWord width (UInt64.ofNat i))
      w[(FFTIndex.twiddleWord n width (UInt64.ofNat i)).toNat]!.1
      (dir * w[(FFTIndex.twiddleWord n width (UInt64.ofNat i)).toNat]!.2) = _
  rw [wordButterfly_eq _ n _ _ _ _ hnmax hlo hhi, hw.1, hw.2.1, hw.2.2, hi64]

theorem stageWith_entries (n width : UInt64) (w : Array (Float × Float)) (dir : Float)
    (ys : Array Float) (h blocks : Nat) (hh : 0 < h)
    (hn : n.toNat = 2 * h * blocks) (hwidth : width.toNat = 2 * h)
    (hnmax : n.toNat ≤ 2 ^ 32) (hsize : ys.size = 2 * n.toNat)
    (i : Nat) (hi : i < h * blocks) :
    entries (stageWith n width w dir ys) (FFTIndex.lower h i) (FFTIndex.upper h i) =
      butterflyValues (entries ys (FFTIndex.lower h i) (FFTIndex.upper h i))
        w[(i % h) * blocks]!.1 (dir * w[(i % h) * blocks]!.2) := by
  rw [stageWith_eq_stageNat _ _ _ _ _ h blocks hh hn hwidth hnmax]
  apply stageNat_entries _ _ _ _ _ hh _ i hi
  rw [hsize, hn]
  ring

theorem radix2With_eq (inv half : Array UInt64) (dir : Float) (xs : Array Float) :
    FFT.radix2With inv half dir xs =
      let n := xs.size.toUInt64 / 2
      let p := FFT.stageCount n
      let w := LeanExe.build (n / 2) fun m => Fourier.twiddleWith inv half n m
      (LeanExe.loop p (copyReversed n p xs, (2 : UInt64)) fun _ state =>
        (stageWith n state.2 w dir state.1, 2 * state.2)).1 := by rfl

theorem stage_loop_induction (p n : UInt64) (w : Array (Float × Float)) (dir : Float)
    (out : Array Float) (hp : p.toNat ≤ 32) (P : Nat → Array Float → Prop)
    (h0 : P 0 out)
    (hstep : ∀ k ys, k < p.toNat → P k ys →
      P (k + 1) (stageWith n (UInt64.ofNat (2 ^ (k + 1))) w dir ys)) :
    P p.toNat (LeanExe.loop p (out, (2 : UInt64)) (fun _ state =>
      (stageWith n state.2 w dir state.1, 2 * state.2))).1 := by
  have h := LeanExe.IR.loop_induction (n := p) (init := (out, (2 : UInt64)))
    (f := fun _ state => (stageWith n state.2 w dir state.1, 2 * state.2))
    (P := fun k (state : Array Float × UInt64) => state.2.toNat = 2 ^ (k + 1) ∧ P k state.1)
    (by exact ⟨rfl, h0⟩)
    (by
      intro k state hk hs
      have hpow : (2 : Nat) ^ (k + 2) ≤ 2 ^ 33 :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have hcap : (2 : Nat) ^ 33 < UInt64.size := by norm_num [UInt64.size]
      have hnext : 2 * state.2.toNat < UInt64.size := by
        rw [hs.1, ← pow_succ']
        exact hpow.trans_lt hcap
      have hwidth : state.2 = UInt64.ofNat (2 ^ (k + 1)) := by
        rw [← hs.1, UInt64.ofNat_toNat]
      refine ⟨?_, ?_⟩
      · rw [UInt64.toNat_mul]
        simp only [UInt64.reduceToNat]
        rw [Nat.mod_eq_of_lt hnext, hs.1, ← pow_succ']
      · rw [hwidth]
        exact hstep k state.1 hk hs.2)
  exact h.2

theorem stageWith_size (n width : UInt64) (w : Array (Float × Float)) (dir : Float)
    (ys : Array Float) : (stageWith n width w dir ys).size = ys.size := by
  unfold stageWith FFT.stageWith
  apply LeanExe.IR.loop_induction (P := fun _ (acc : Array Float) => acc.size = ys.size)
  · rfl
  · intro i acc _ hs
    simpa only [Array.size_set!] using hs

theorem copyReversed_size (n p : UInt64) (xs : Array Float) (hn : n.toNat ≤ 2 ^ 32) :
    (copyReversed n p xs).size = 2 * n.toNat := by
  have hdouble : (2 * n).toNat = 2 * n.toNat := by
    rw [UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    norm_num at hn ⊢
    omega
  unfold copyReversed FFT.copyReversed
  apply LeanExe.IR.loop_induction (P := fun _ (acc : Array Float) => acc.size = 2 * n.toNat)
  · rw [LeanExe.IR.build_size, hdouble]
  · intro i acc _ hs
    simpa only [Array.size_set!] using hs

def reverseIndex (p : UInt64) (j : Nat) : Nat := (FFT.reverseBits p (UInt64.ofNat j)).toNat

theorem reverseIndex_lt (p : UInt64) (j : Nat) (hp : p.toNat ≤ 32) :
    reverseIndex p j < 2 ^ p.toNat := FFTBits.reverseBits_lt _ _ hp

theorem reverseIndex_eq_reverseNat (p : UInt64) (j : Nat) (hp : p.toNat ≤ 32)
    (hj : j < 2 ^ p.toNat) : reverseIndex p j = FFTBits.reverseNat p.toNat j := by
  unfold reverseIndex
  rw [FFTBits.reverseBits_toNat _ _ hp, UInt64.toNat_ofNat_of_lt']
  have hpow : (2 : Nat) ^ p.toNat ≤ 2 ^ 32 := Nat.pow_le_pow_right (by omega) hp
  exact (hj.trans_le hpow).trans (by norm_num [UInt64.size])

theorem reverseIndex_involutive (p : UInt64) (j : Nat) (hp : p.toNat ≤ 32)
    (hj : j < 2 ^ p.toNat) : reverseIndex p (reverseIndex p j) = j := by
  rw [reverseIndex_eq_reverseNat p _ hp (reverseIndex_lt p j hp),
    reverseIndex_eq_reverseNat p j hp hj, FFTBits.reverseNat_involutive _ _ hj]

theorem reverseIndex_injective (p : UInt64) (hp : p.toNat ≤ 32) (j k : Nat)
    (hj : j < 2 ^ p.toNat) (hk : k < 2 ^ p.toNat) : reverseIndex p j = reverseIndex p k → j = k := by
  intro heq
  have h := congrArg (reverseIndex p) heq
  rwa [reverseIndex_involutive p j hp hj, reverseIndex_involutive p k hp hk] at h

theorem copyReversed_entries (n p : UInt64) (xs : Array Float) (hp : p.toNat ≤ 32)
    (hn : n.toNat = 2 ^ p.toNat) :
    (copyReversed n p xs).size = 2 * n.toNat ∧
      ∀ j, j < n.toNat →
        (copyReversed n p xs)[2 * reverseIndex p j]! = xs[2 * j]! ∧
        (copyReversed n p xs)[2 * reverseIndex p j + 1]! = xs[2 * j + 1]! := by
  have hn32 : n.toNat ≤ 2 ^ 32 := by rw [hn]; exact Nat.pow_le_pow_right (by omega) hp
  have hdouble : (2 * n).toNat = 2 * n.toNat := by
    rw [UInt64.toNat_mul]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    norm_num at hn32 ⊢
    omega
  unfold copyReversed FFT.copyReversed
  apply LeanExe.IR.loop_induction (P := fun k (acc : Array Float) =>
    acc.size = 2 * n.toNat ∧ ∀ j, j < k →
      acc[2 * reverseIndex p j]! = xs[2 * j]! ∧
      acc[2 * reverseIndex p j + 1]! = xs[2 * j + 1]!)
  · exact ⟨by rw [LeanExe.IR.build_size, hdouble], by omega⟩
  · intro k acc hk hs
    dsimp only
    have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by
      norm_num [UInt64.size]
      norm_num at hn32
      omega)
    have hkw : UInt64.ofNat k < n := UInt64.lt_iff_toNat_lt.mpr (by rw [hk64]; exact hk)
    have hrk : reverseIndex p k < n.toNat := by rw [hn]; exact reverseIndex_lt p k hp
    have hrkw : FFT.reverseBits p (UInt64.ofNat k) < n := UInt64.lt_iff_toNat_lt.mpr hrk
    rw [FourierLoop.twice_toNat n _ hn32 hkw, FourierLoop.twice_add_one_toNat n _ hn32 hkw,
      FourierLoop.twice_toNat n _ hn32 hrkw, FourierLoop.twice_add_one_toNat n _ hn32 hrkw, hk64]
    change ((acc.set! (2 * reverseIndex p k) xs[2 * k]!).set!
        (2 * reverseIndex p k + 1) xs[2 * k + 1]!).size = 2 * n.toNat ∧
      ∀ j, j < k + 1 →
        ((acc.set! (2 * reverseIndex p k) xs[2 * k]!).set!
          (2 * reverseIndex p k + 1) xs[2 * k + 1]!)[2 * reverseIndex p j]! = xs[2 * j]! ∧
        ((acc.set! (2 * reverseIndex p k) xs[2 * k]!).set!
          (2 * reverseIndex p k + 1) xs[2 * k + 1]!)[2 * reverseIndex p j + 1]! = xs[2 * j + 1]!
    refine ⟨by simpa only [Array.size_set!] using hs.1, ?_⟩
    intro j hj
    by_cases hjk : j = k
    · subst j
      constructor
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_self _ _ _ (by rw [hs.1]; omega)]
      · rw [Array.getElem!_set!_self _ _ _ (by rw [Array.size_set!, hs.1]; omega)]
    · have hjold : j < k := by omega
      have hrne : reverseIndex p j ≠ reverseIndex p k := by
        intro heq
        exact hjk (reverseIndex_injective p hp j k (by rw [← hn]; omega)
          (by rw [← hn]; exact hk) heq)
      change _[2 * reverseIndex p j]! = _ ∧ _[2 * reverseIndex p j + 1]! = _
      constructor
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact (hs.2 j hjold).1
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact (hs.2 j hjold).2

theorem copyReversed_get_real (n p : UInt64) (xs : Array Float) (hp : p.toNat ≤ 32)
    (hn : n.toNat = 2 ^ p.toNat) (k : Nat) (hk : k < n.toNat) :
    (copyReversed n p xs)[2 * k]! = xs[2 * FFTBits.reverseNat p.toNat k]! := by
  have h := ((copyReversed_entries n p xs hp hn).2 (reverseIndex p k)
    (by rw [hn]; exact reverseIndex_lt p k hp)).1
  rwa [reverseIndex_involutive p k hp (by rw [← hn]; exact hk),
    reverseIndex_eq_reverseNat p k hp (by rw [← hn]; exact hk)] at h

theorem copyReversed_get_imag (n p : UInt64) (xs : Array Float) (hp : p.toNat ≤ 32)
    (hn : n.toNat = 2 ^ p.toNat) (k : Nat) (hk : k < n.toNat) :
    (copyReversed n p xs)[2 * k + 1]! = xs[2 * FFTBits.reverseNat p.toNat k + 1]! := by
  have h := ((copyReversed_entries n p xs hp hn).2 (reverseIndex p k)
    (by rw [hn]; exact reverseIndex_lt p k hp)).2
  rwa [reverseIndex_involutive p k hp (by rw [← hn]; exact hk),
    reverseIndex_eq_reverseNat p k hp (by rw [← hn]; exact hk)] at h

theorem radix2With_size (inv half : Array UInt64) (dir : Float) (xs : Array Float)
    (hn : xs.size / 2 ≤ 2 ^ 32) : (FFT.radix2With inv half dir xs).size = 2 * (xs.size / 2) := by
  have hnWord : (xs.size.toUInt64 / 2).toNat ≤ 2 ^ 32 := FourierLoop.nWord_le xs hn
  have hnNat : (xs.size.toUInt64 / 2).toNat = xs.size / 2 := FourierLoop.nWord_toNat xs hn
  rw [radix2With_eq]
  dsimp only
  have h := LeanExe.IR.loop_induction
    (n := FFT.stageCount (xs.size.toUInt64 / 2))
    (init := (copyReversed (xs.size.toUInt64 / 2) (FFT.stageCount (xs.size.toUInt64 / 2)) xs,
      (2 : UInt64)))
    (f := fun _ state =>
      (stageWith (xs.size.toUInt64 / 2) state.2
        (LeanExe.build (xs.size.toUInt64 / 2 / 2) fun m =>
          Fourier.twiddleWith inv half (xs.size.toUInt64 / 2) m) dir state.1, 2 * state.2))
    (P := fun _ (state : Array Float × UInt64) => state.1.size = 2 * (xs.size / 2))
    (by rw [copyReversed_size _ _ _ hnWord, hnNat])
    (by intro i state _ hs; rw [stageWith_size]; exact hs)
  exact h

theorem fourierTransformWith_size (inv half : Array UInt64) (dir : Float) (xs : Array Float)
    (hn : xs.size / 2 ≤ 2 ^ 32) :
    (Fourier.transformWith inv half dir xs).size = 2 * (xs.size / 2) := by
  have hnNat : (xs.size.toUInt64 / 2).toNat = xs.size / 2 := FourierLoop.nWord_toNat xs hn
  have hdouble : (2 * (xs.size.toUInt64 / 2)).toNat = 2 * (xs.size / 2) := by
    rw [UInt64.toNat_mul, hnNat]
    simp only [UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    norm_num at hn ⊢
    omega
  unfold Fourier.transformWith
  apply LeanExe.IR.loop_induction (P := fun _ (acc : Array Float) => acc.size = 2 * (xs.size / 2))
  · rw [LeanExe.IR.build_size, hdouble]
  · intro i acc _ hs
    simpa only [Array.size_set!] using hs

theorem fftTransformWith_size (inv half : Array UInt64) (dir : Float) (xs : Array Float)
    (hn : xs.size / 2 ≤ 2 ^ 32) :
    (FFT.fftTransformWith inv half dir xs).size = 2 * (xs.size / 2) := by
  unfold FFT.fftTransformWith
  dsimp only
  split
  · exact radix2With_size inv half dir xs hn
  · exact fourierTransformWith_size inv half dir xs hn

theorem fftTransformWith_eq_fourier (inv half : Array UInt64) (dir : Float) (xs : Array Float)
    (h : FFT.isRadix2 (xs.size.toUInt64 / 2) = false) :
    FFT.fftTransformWith inv half dir xs = Fourier.transformWith inv half dir xs := by
  simp only [FFT.fftTransformWith, h, Bool.false_eq_true, ite_false]

theorem inverseWith_eq_map (inv half : Array UInt64) (xs : Array Float)
    (hn : xs.size / 2 ≤ 2 ^ 32) :
    FFT.inverseWith inv half xs = (FFT.fftTransformWith inv half 1.0 xs).map
      (fun y => y / (xs.size.toUInt64 / 2).toFloat) := by
  unfold FFT.inverseWith
  dsimp only
  apply FourierInverseLoop.loop_map (FFT.fftTransformWith inv half 1.0 xs)
    (fun y => y / (xs.size.toUInt64 / 2).toFloat)
  rw [fftTransformWith_size inv half 1.0 xs hn]
  norm_num [UInt64.size]
  norm_num at hn
  omega

theorem inverse_size (xs : Array Float) (hn : xs.size / 2 ≤ 2 ^ 32) :
    (FFT.inverse xs).size = 2 * (xs.size / 2) := by
  rw [FFT.inverse, inverseWith_eq_map _ _ xs hn, Array.size_map, fftTransformWith_size _ _ _ xs hn]

theorem inverseWith_get (inv half : Array UInt64) (xs : Array Float)
    (hn : xs.size / 2 ≤ 2 ^ 32) (i : Nat) (hi : i < 2 * (xs.size / 2)) :
    (FFT.inverseWith inv half xs)[i]! =
      (FFT.fftTransformWith inv half 1.0 xs)[i]! / (xs.size.toUInt64 / 2).toFloat := by
  rw [inverseWith_eq_map inv half xs hn]
  have hinput : i < (FFT.fftTransformWith inv half 1.0 xs).size := by
    rw [fftTransformWith_size inv half 1.0 xs hn]
    exact hi
  rw [getElem!_pos _ i (by simpa only [Array.size_map] using hinput),
    Array.getElem_map, getElem!_pos _ i hinput]

theorem powerSpectrum_eq_build (samples : Array Float) :
    FFT.powerSpectrum samples =
      LeanExe.build (if samples.size.toUInt64 == 0 then 0 else samples.size.toUInt64 / 2 + 1)
        (fun k =>
          let ys := FFT.fft (FourierPowerEmbedding.embed samples)
          let a := ys[(2 * k).toNat]!
          let b := ys[(2 * k + 1).toNat]!
          a * a + b * b) := by rfl

theorem powerSpectrum_size (samples : Array Float) (hn : samples.size ≤ 2 ^ 32) :
    (FFT.powerSpectrum samples).size = FourierPowerEmbedding.powerCount samples.size := by
  rw [powerSpectrum_eq_build, LeanExe.IR.build_size]
  have h := FourierPowerEmbedding.powerSpectrum_size samples hn
  rwa [FourierPowerEmbedding.powerSpectrum_eq_build, LeanExe.IR.build_size] at h

theorem powerSpectrum_get (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (k : Nat) (hk : k < FourierPowerEmbedding.powerCount samples.size) :
    (FFT.powerSpectrum samples)[k]! =
      (FFT.fft (FourierPowerEmbedding.embed samples))[2 * k]! *
        (FFT.fft (FourierPowerEmbedding.embed samples))[2 * k]! +
      (FFT.fft (FourierPowerEmbedding.embed samples))[2 * k + 1]! *
        (FFT.fft (FourierPowerEmbedding.embed samples))[2 * k + 1]! := by
  have hkN : k < samples.size := by
    unfold FourierPowerEmbedding.powerCount at hk
    split at hk <;> omega
  have hk64 : (UInt64.ofNat k).toNat = k := UInt64.toNat_ofNat_of_lt' (by
    norm_num [UInt64.size]
    norm_num at hn
    omega)
  have hnWord : samples.size.toUInt64.toNat ≤ 2 ^ 32 := by
    rw [FourierPowerEmbedding.sampleWord_toNat samples hn]
    exact hn
  have hkWord : UInt64.ofNat k < samples.size.toUInt64 := UInt64.lt_iff_toNat_lt.mpr (by
    rw [hk64, FourierPowerEmbedding.sampleWord_toNat samples hn]
    exact hkN)
  rw [powerSpectrum_eq_build, LeanExe.IR.build_get (by
    have hc := FourierPowerEmbedding.powerSpectrum_size samples hn
    rw [FourierPowerEmbedding.powerSpectrum_eq_build, LeanExe.IR.build_size] at hc
    rw [hc]
    exact hk), FourierLoop.twice_toNat _ _ hnWord hkWord,
    FourierLoop.twice_add_one_toNat _ _ hnWord hkWord, hk64]

theorem fft_eq_dft (xs : Array Float) (h : FFT.isRadix2 (xs.size.toUInt64 / 2) = false) :
    FFT.fft xs = Fourier.dft xs := by
  exact fftTransformWith_eq_fourier Trig.invPi Trig.halfPi (-1.0) xs h

theorem inverseWith_eq_fourier (inv half : Array UInt64) (xs : Array Float)
    (h : FFT.isRadix2 (xs.size.toUInt64 / 2) = false) :
    FFT.inverseWith inv half xs = Fourier.inverseWith inv half xs := by
  unfold FFT.inverseWith Fourier.inverseWith
  rw [fftTransformWith_eq_fourier inv half 1.0 xs h]

theorem inverse_eq_fourier (xs : Array Float)
    (h : FFT.isRadix2 (xs.size.toUInt64 / 2) = false) : FFT.inverse xs = Fourier.inverse xs :=
  inverseWith_eq_fourier Trig.invPi Trig.halfPi xs h

theorem powerSpectrumWith_eq_fourier (inv half : Array UInt64) (samples : Array Float)
    (hn : samples.size ≤ 2 ^ 32) (h : FFT.isRadix2 samples.size.toUInt64 = false) :
    FFT.powerSpectrumWith inv half samples = Fourier.powerSpectrumWith inv half samples := by
  have hnWord : (FourierPowerEmbedding.embed samples).size.toUInt64 / 2 =
      samples.size.toUInt64 := by
    apply UInt64.toNat_inj.mp
    change (FourierLoop.nWord (FourierPowerEmbedding.embed samples)).toNat = _
    rw [FourierLoop.nWord_toNat _ (by
      change (FourierPowerEmbedding.embed samples).size / 2 ≤ 2 ^ 32
      rw [FourierPowerEmbedding.embed_nSamples samples hn]
      exact hn), FourierPowerEmbedding.sampleWord_toNat samples hn]
    exact FourierPowerEmbedding.embed_nSamples samples hn
  unfold FFT.powerSpectrumWith Fourier.powerSpectrumWith
  dsimp only
  have hf := fftTransformWith_eq_fourier inv half (-1.0) (FourierPowerEmbedding.embed samples)
    (by rw [hnWord]; exact h)
  dsimp only [FourierPowerEmbedding.embed] at hf
  rw [hf]

theorem powerSpectrum_eq_fourier (samples : Array Float) (hn : samples.size ≤ 2 ^ 32)
    (h : FFT.isRadix2 samples.size.toUInt64 = false) :
    FFT.powerSpectrum samples = Fourier.powerSpectrum samples :=
  powerSpectrumWith_eq_fourier Trig.invPi Trig.halfPi samples hn h

theorem fft_empty : FFT.fft #[] = #[] := by rfl

theorem inverse_empty : FFT.inverse #[] = #[] := by rfl

theorem powerSpectrum_empty : FFT.powerSpectrum #[] = #[] := by rfl

#print axioms radix2With_eq
#print axioms stage_loop_induction
#print axioms copyReversed_entries
#print axioms stageWith_entries
#print axioms fftTransformWith_size
#print axioms fft_eq_dft
#print axioms inverse_eq_fourier
#print axioms inverseWith_get
#print axioms powerSpectrum_get
#print axioms powerSpectrum_eq_fourier

end Verified.Examples.FFTLoop
