import Project.Gpt2QuantizedCached.Numerical.TensorBounds
import Project.Gpt2CachedStep.GeluRangeCertificate

namespace Project.Gpt2QuantizedCached.Numerical.GeluRange
open LeanExe.Models.Gpt2 Project.Gpt2CachedStep

noncomputable def parameters (qp rp : GeluRangeCertificate.Parameters) : Activate.Parameters :=
  ⟨fun _ => GeluRangeCertificate.bounds qp, fun _ => GeluRangeCertificate.bounds rp⟩

theorem sound (qi ri : ByteArray) (n : Nat) (qp rp : GeluRangeCertificate.Parameters)
    (hq : ∀ i < n, GeluRangeCertificate.check (word qi i) qp = true)
    (hr : ∀ i < n, GeluRangeCertificate.check (word ri i) rp = true) :
    Activate.Ranges qi ri n (parameters qp rp) := by
  intro i hi
  have hQ := GeluRangeCertificate.sound (word qi i) qp (hq i hi)
  have hR := GeluRangeCertificate.sound (word ri i) rp (hr i hi)
  exact ⟨hQ.1, hR.1, hQ.2, hR.2⟩

#print axioms sound
end Project.Gpt2QuantizedCached.Numerical.GeluRange
