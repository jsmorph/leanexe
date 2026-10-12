import Verified.Examples.Fourier
import LeanExe.IR.Combinators

namespace Verified.Examples.FourierLoop

def nSamples (xs : Array Float) : Nat := xs.size / 2

def nWord (xs : Array Float) : UInt64 := xs.size.toUInt64 / 2

def realTerm (xs : Array Float) (k j : UInt64) : Float :=
  let t := Fourier.twiddle (nWord xs) (j * k % nWord xs)
  let c := t.1
  let d := (-1.0) * t.2
  let a := xs[(2 * j).toNat]!
  let b := xs[(2 * j + 1).toNat]!
  a * c - b * d

def imagTerm (xs : Array Float) (k j : UInt64) : Float :=
  let t := Fourier.twiddle (nWord xs) (j * k % nWord xs)
  let c := t.1
  let d := (-1.0) * t.2
  let a := xs[(2 * j).toNat]!
  let b := xs[(2 * j + 1).toNat]!
  a * d + b * c

def realAccum (xs : Array Float) (k : UInt64) : Float :=
  LeanExe.loop (nWord xs) (0.0 : Float) fun j acc => acc + realTerm xs k j

def imagAccum (xs : Array Float) (k : UInt64) : Float :=
  LeanExe.loop (nWord xs) (0.0 : Float) fun j acc => acc + imagTerm xs k j

def pairAccum (xs : Array Float) (k : UInt64) : Float × Float :=
  LeanExe.loop (nWord xs) ((0.0 : Float), (0.0 : Float)) fun j acc =>
    (acc.1 + realTerm xs k j, acc.2 + imagTerm xs k j)

theorem pairAccum_real (xs : Array Float) (k : UInt64) :
    (pairAccum xs k).1 = realAccum xs k := by
  exact (Verified.Reflect.loop_map Prod.fst (nWord xs) ((0.0 : Float), (0.0 : Float))
    (fun j acc => (acc.1 + realTerm xs k j, acc.2 + imagTerm xs k j))
    (fun j acc => acc + realTerm xs k j) (fun _ _ => rfl)).symm

theorem pairAccum_imag (xs : Array Float) (k : UInt64) :
    (pairAccum xs k).2 = imagAccum xs k := by
  exact (Verified.Reflect.loop_map Prod.snd (nWord xs) ((0.0 : Float), (0.0 : Float))
    (fun j acc => (acc.1 + realTerm xs k j, acc.2 + imagTerm xs k j))
    (fun j acc => acc + imagTerm xs k j) (fun _ _ => rfl)).symm

theorem nWord_toNat (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32) :
    (nWord xs).toNat = nSamples xs := by
  have hs : xs.size < UInt64.size := by
    dsimp [nSamples] at hn
    norm_num [UInt64.size]
    omega
  simp only [nWord, UInt64.toNat_div, UInt64.reduceToNat, Nat.toUInt64_eq,
    UInt64.toNat_ofNat_of_lt' hs]
  rfl

theorem nWord_le (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32) :
    (nWord xs).toNat ≤ 2 ^ 32 := by
  rw [nWord_toNat xs hn]
  exact hn

theorem twice_toNat (n j : UInt64) (hn : n.toNat ≤ 2 ^ 32) (hj : j < n) :
    (2 * j).toNat = 2 * j.toNat := by
  have hj' : j.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp hj
  simp only [UInt64.toNat_mul, UInt64.reduceToNat]
  apply Nat.mod_eq_of_lt
  norm_num at hn ⊢
  omega

theorem twice_add_one_toNat (n j : UInt64) (hn : n.toNat ≤ 2 ^ 32) (hj : j < n) :
    (2 * j + 1).toNat = 2 * j.toNat + 1 := by
  rw [UInt64.toNat_add, twice_toNat n j hn hj]
  simp only [UInt64.reduceToNat]
  apply Nat.mod_eq_of_lt
  have hj' : j.toNat < n.toNat := UInt64.lt_iff_toNat_lt.mp hj
  norm_num at hn ⊢
  omega

theorem product_mod_toNat (n j k : UInt64) (hn : n.toNat ≤ 2 ^ 32)
    (hj : j < n) (hk : k < n) :
    (j * k % n).toNat = j.toNat * k.toNat % n.toNat := by
  have hj' : j.toNat < 2 ^ 32 :=
    lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp hj) hn
  have hk' : k.toNat < 2 ^ 32 :=
    lt_of_lt_of_le (UInt64.lt_iff_toNat_lt.mp hk) hn
  have hprod : j.toNat * k.toNat < 2 ^ 64 := by
    calc
      j.toNat * k.toNat < (2 ^ 32) * (2 ^ 32) :=
        Nat.mul_lt_mul_of_lt_of_lt hj' hk'
      _ = 2 ^ 64 := by norm_num
  rw [UInt64.toNat_mod, UInt64.toNat_mul, Nat.mod_eq_of_lt hprod]

theorem sample_real_index (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (j : UInt64) (hj : j < nWord xs) : (2 * j).toNat = 2 * j.toNat :=
  twice_toNat _ _ (nWord_le xs hn) hj

theorem sample_imag_index (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (j : UInt64) (hj : j < nWord xs) : (2 * j + 1).toNat = 2 * j.toNat + 1 :=
  twice_add_one_toNat _ _ (nWord_le xs hn) hj

theorem phase_index (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (j k : UInt64) (hj : j < nWord xs) (hk : k < nWord xs) :
    (j * k % nWord xs).toNat = j.toNat * k.toNat % nSamples xs := by
  rw [product_mod_toNat _ _ _ (nWord_le xs hn) hj hk, nWord_toNat xs hn]

theorem ofNat_lt_nWord (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (j : Nat) (hj : j < nSamples xs) : UInt64.ofNat j < nWord xs := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_ofNat_of_lt', nWord_toNat xs hn]
  · exact hj
  · norm_num [UInt64.size]
    norm_num at hn
    omega

theorem dft_eq_loop (xs : Array Float) :
    Fourier.dft xs = LeanExe.loop (nWord xs)
      (LeanExe.build (2 * nWord xs) fun _ => (0.0 : Float))
      (fun k out => (out.set! (2 * k).toNat (pairAccum xs k).1).set!
        (2 * k + 1).toNat (pairAccum xs k).2) := by
  unfold Fourier.dft Fourier.dftWith Fourier.transformWith
  dsimp only
  apply LeanExe.IR.loop_congr
  intro k hk out
  have hinner :
      LeanExe.loop (nWord xs) ((0.0 : Float), (0.0 : Float)) (fun j acc =>
        let t := (LeanExe.build (nWord xs) fun m =>
          Fourier.twiddleWith Trig.invPi Trig.halfPi (nWord xs) m)[(j * UInt64.ofNat k % nWord xs).toNat]!
        (acc.1 + (xs[(2 * j).toNat]! * t.1 - xs[(2 * j + 1).toNat]! * ((-1.0) * t.2)),
         acc.2 + (xs[(2 * j).toNat]! * ((-1.0) * t.2) + xs[(2 * j + 1).toNat]! * t.1))) =
        pairAccum xs (UInt64.ofNat k) := by
    apply LeanExe.IR.loop_congr
    intro j hj acc
    have hmod : (UInt64.ofNat j * UInt64.ofNat k % nWord xs).toNat < (nWord xs).toNat := by
      rw [UInt64.toNat_mod]
      exact Nat.mod_lt _ (by omega)
    rw [LeanExe.IR.build_get hmod, UInt64.ofNat_toNat]
    rfl
  exact congrArg (fun s : Float × Float =>
    (out.set! (2 * UInt64.ofNat k).toNat s.1).set! (2 * UInt64.ofNat k + 1).toNat s.2) hinner

private theorem loop_entries (n : UInt64) (hn : n.toNat ≤ 2 ^ 32)
    (f : UInt64 → Float × Float) :
    let out := LeanExe.loop n (LeanExe.build (2 * n) fun _ => (0.0 : Float))
      (fun k out => (out.set! (2 * k).toNat (f k).1).set! (2 * k + 1).toNat (f k).2)
    out.size = 2 * n.toNat ∧ ∀ k, k < n.toNat →
      out[2 * k]! = (f (UInt64.ofNat k)).1 ∧
      out[2 * k + 1]! = (f (UInt64.ofNat k)).2 := by
  have hdouble : (2 * n).toNat = 2 * n.toNat := by
    simp only [UInt64.toNat_mul, UInt64.reduceToNat]
    apply Nat.mod_eq_of_lt
    norm_num at hn ⊢
    omega
  dsimp only
  apply LeanExe.IR.loop_induction
    (fun i (out : Array Float) => out.size = 2 * n.toNat ∧ ∀ k, k < i →
      out[2 * k]! = (f (UInt64.ofNat k)).1 ∧
      out[2 * k + 1]! = (f (UInt64.ofNat k)).2)
  · exact ⟨by rw [LeanExe.IR.build_size, hdouble], by omega⟩
  · intro i out hi hprev
    have hi64 : (UInt64.ofNat i).toNat = i := UInt64.toNat_ofNat_of_lt' (by
      norm_num [UInt64.size]
      norm_num at hn
      omega)
    have hiword : UInt64.ofNat i < n := by rw [UInt64.lt_iff_toNat_lt, hi64]; exact hi
    rw [twice_toNat n _ hn hiword, twice_add_one_toNat n _ hn hiword, hi64]
    refine ⟨by simpa only [Array.size_set!] using hprev.1, ?_⟩
    intro k hk
    by_cases hki : k = i
    · subst k
      constructor
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_self _ _ _ (by omega)]
      · rw [Array.getElem!_set!_self _ _ _ (by simpa only [Array.size_set!] using (show 2 * i + 1 < out.size by omega))]
    · have hki' : k < i := by omega
      constructor
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact (hprev.2 k hki').1
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
        exact (hprev.2 k hki').2

theorem dft_size (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32) :
    (Fourier.dft xs).size = 2 * nSamples xs := by
  rw [dft_eq_loop]
  have h := (loop_entries (nWord xs) (nWord_le xs hn) (pairAccum xs)).1
  simpa only [nWord_toNat xs hn] using h

theorem dft_get_real (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (k : Nat) (hk : k < nSamples xs) :
    (Fourier.dft xs)[2 * k]! = realAccum xs (UInt64.ofNat k) := by
  rw [dft_eq_loop]
  have hk' : k < (nWord xs).toNat := by rw [nWord_toNat xs hn]; exact hk
  exact ((loop_entries (nWord xs) (nWord_le xs hn) (pairAccum xs)).2 k hk').1.trans
    (pairAccum_real xs _)

theorem dft_get_imag (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (k : Nat) (hk : k < nSamples xs) :
    (Fourier.dft xs)[2 * k + 1]! = imagAccum xs (UInt64.ofNat k) := by
  rw [dft_eq_loop]
  have hk' : k < (nWord xs).toNat := by rw [nWord_toNat xs hn]; exact hk
  exact ((loop_entries (nWord xs) (nWord_le xs hn) (pairAccum xs)).2 k hk').2.trans
    (pairAccum_imag xs _)

#print axioms nWord_toNat
#print axioms sample_real_index
#print axioms sample_imag_index
#print axioms phase_index
#print axioms dft_eq_loop
#print axioms dft_size
#print axioms dft_get_real
#print axioms dft_get_imag

end Verified.Examples.FourierLoop
