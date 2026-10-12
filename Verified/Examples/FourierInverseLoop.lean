import Verified.Examples.FourierPositive

namespace Verified.Examples.FourierInverseLoop

open FourierLoop

theorem loop_map {α : Type} [Inhabited α] (ys : Array α) (f : α → α)
    (hs : ys.size < UInt64.size) :
    LeanExe.loop ys.size.toUInt64 ys (fun i acc => acc.set! i.toNat (f acc[i.toNat]!)) =
      ys.map f := by
  let out := LeanExe.loop ys.size.toUInt64 ys
    (fun i acc => acc.set! i.toNat (f acc[i.toNat]!))
  have hsize : ys.size.toUInt64.toNat = ys.size := by
    simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' hs]
  have hout : out.size = ys.size ∧ ∀ k, k < ys.size →
        out[k]! = if k < ys.size.toUInt64.toNat then f ys[k]! else ys[k]! := by
    dsimp only [out]
    apply LeanExe.IR.loop_induction (P := fun i (out : Array α) =>
      out.size = ys.size ∧ ∀ k, k < ys.size →
        out[k]! = if k < i then f ys[k]! else ys[k]!)
    · exact ⟨rfl, fun k _ => by simp⟩
    · intro i acc hi hacc
      rw [hsize] at hi
      have hi64 : (UInt64.ofNat i).toNat = i :=
        UInt64.toNat_ofNat_of_lt' (hi.trans hs)
      rw [hi64]
      have hentry := hacc.2 i hi
      rw [ite_eq_right (lt_irrefl i)] at hentry
      rw [hentry]
      refine ⟨by simpa only [Array.size_set!] using hacc.1, ?_⟩
      intro k hk
      by_cases hki : k = i
      · subst k
        rw [Array.getElem!_set!_self _ _ _ (by omega)]
        simp
      · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hki)]
        rw [hacc.2 k hk]
        have he : k < i + 1 ↔ k < i := by omega
        simp only [he]
  rw [hsize] at hout
  apply Array.ext (by simpa only [Array.size_map] using hout.1)
  intro i hi himap
  have hiys : i < ys.size := by simpa only [Array.size_map] using himap
  have hentry := hout.2 i hiys
  rw [ite_eq_left hiys] at hentry
  simpa only [getElem!_pos out i hi, getElem!_pos ys i hiys, Array.getElem_map] using hentry

theorem inverse_eq_map (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32) :
    Fourier.inverse xs = (FourierPositive.transform xs).map
      (fun y => y / (nWord xs).toFloat) := by
  unfold Fourier.inverse Fourier.inverseWith
  change LeanExe.loop (FourierPositive.transform xs).size.toUInt64 (FourierPositive.transform xs)
    (fun i acc => acc.set! i.toNat (acc[i.toNat]! / (nWord xs).toFloat)) = _
  apply loop_map (FourierPositive.transform xs) (fun y => y / (nWord xs).toFloat)
  change (Fourier.transformWith Trig.invPi Trig.halfPi 1.0 xs).size < UInt64.size
  rw [transform_size 1.0 xs hn]
  norm_num [UInt64.size]
  norm_num at hn
  omega

theorem inverse_size (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32) :
    (Fourier.inverse xs).size = 2 * nSamples xs := by
  rw [inverse_eq_map xs hn, Array.size_map]
  exact transform_size 1.0 xs hn

theorem inverse_get_real (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (k : Nat) (hk : k < nSamples xs) :
    (Fourier.inverse xs)[2 * k]! =
      (FourierPositive.transform xs)[2 * k]! / (nWord xs).toFloat := by
  rw [inverse_eq_map xs hn]
  have hi : 2 * k < (FourierPositive.transform xs).size := by
    change 2 * k < (Fourier.transformWith Trig.invPi Trig.halfPi 1.0 xs).size
    rw [transform_size 1.0 xs hn]
    omega
  rw [getElem!_pos ((FourierPositive.transform xs).map
      (fun y => y / (nWord xs).toFloat)) (2 * k) (by simpa only [Array.size_map] using hi),
    Array.getElem_map, getElem!_pos (FourierPositive.transform xs) (2 * k) hi]

theorem inverse_get_imag (xs : Array Float) (hn : nSamples xs ≤ 2 ^ 32)
    (k : Nat) (hk : k < nSamples xs) :
    (Fourier.inverse xs)[2 * k + 1]! =
      (FourierPositive.transform xs)[2 * k + 1]! / (nWord xs).toFloat := by
  rw [inverse_eq_map xs hn]
  have hi : 2 * k + 1 < (FourierPositive.transform xs).size := by
    change 2 * k + 1 < (Fourier.transformWith Trig.invPi Trig.halfPi 1.0 xs).size
    rw [transform_size 1.0 xs hn]
    omega
  rw [getElem!_pos ((FourierPositive.transform xs).map
      (fun y => y / (nWord xs).toFloat)) (2 * k + 1) (by simpa only [Array.size_map] using hi),
    Array.getElem_map, getElem!_pos (FourierPositive.transform xs) (2 * k + 1) hi]

#print axioms loop_map
#print axioms inverse_eq_map
#print axioms inverse_size
#print axioms inverse_get_real
#print axioms inverse_get_imag

end Verified.Examples.FourierInverseLoop
