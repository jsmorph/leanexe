import Project.SpectralKL.Executable
import Project.SpectralKL.CertificateRun
import Project.SpectralKL.ScalarEstimator
import Project.SpectralKL.MatrixAuto
import Project.SpectralKL.WordAccelerated

-- Inspect the specification, public implication, source connection and axioms.
-- The proof build is a separate command documented in docs/spectral-kl.md.
#print Project.SpectralKL.MatrixAccelerated.computeMoments
#check Project.SpectralKL.MatrixAccelerated.compute_correct
#check Project.SpectralKL.MatrixAccelerated.compute_returned_error
#print axioms Project.SpectralKL.MatrixAccelerated.compute_correct
#print axioms Project.SpectralKL.MatrixAccelerated.compute_returned_error
#print Project.SpectralKL.WordMoments.Valid
#print Project.SpectralKL.WordShader.Layout
#check Project.SpectralKL.WordShader.source_parses
#check Project.SpectralKL.WordShader.sourceTotals_eq
#check Project.SpectralKL.WordAccelerated.compute_correct
#check Project.SpectralKL.WordAccelerated.computeSource_correct
#print axioms Project.SpectralKL.WordShader.source_parses
#print axioms Project.SpectralKL.WordAccelerated.compute_correct
#print axioms Project.SpectralKL.WordAccelerated.computeSource_correct
#print Project.SpectralKL.MatrixGeneral.Valid
#print Project.SpectralKL.MatrixGeneral.computeAuto
#check Project.SpectralKL.MatrixGeneral.computeAuto_correct
#check Project.SpectralKL.MatrixGeneral.computeAuto_returned_error
#print axioms Project.SpectralKL.MatrixGeneral.computeAuto_correct
#print axioms Project.SpectralKL.MatrixGeneral.computeAuto_returned_error
#print Project.SpectralKL.MatrixEstimator.Valid
#check Project.SpectralKL.MatrixEstimator.compute_correct
#check Project.SpectralKL.MatrixEstimator.computeAdaptive_correct
#check Project.SpectralKL.MatrixEstimator.computeAdaptive_returned_error
#print axioms Project.SpectralKL.MatrixEstimator.computeAdaptive_correct
#print axioms Project.SpectralKL.MatrixEstimator.computeAdaptive_returned_error
#print Project.SpectralKL.Scalar.ValidSamples
#print Project.SpectralKL.Scalar.ValidRidge
#print Project.SpectralKL.Scalar.regularizedIntegral
#print Project.SpectralKL.Scalar.sampleIntegral
#print LeanExe.Examples.SpectralKL.fromBoundedSamples
#print LeanExe.Examples.SpectralKL.fromUnitSamples
#check Project.SpectralKL.Scalar.fromBoundedSamples_correct
#print axioms Project.SpectralKL.Scalar.fromBoundedSamples_correct
#check Project.SpectralKL.Scalar.fromUnitSamples_correct
#print axioms Project.SpectralKL.Scalar.fromUnitSamples_correct
#print Project.SpectralKL.Certificate.target
#print Project.SpectralKL.Certificate.integrand
#print Project.SpectralKL.Samples.system
#print Project.SpectralKL.Samples.mean
#print Project.SpectralKL.Samples.moment
#check Project.SpectralKL.Certificate.accepts_sound
#check Project.SpectralKL.Certificate.Fast.enclose_eq
#check Project.SpectralKL.Certificate.Fast.certify
#check Project.SpectralKL.Certificate.Fast.certify_score
#check Project.SpectralKL.Certificate.Fast.accepted_error
#check Project.SpectralKL.Executable.kernel40_accepted
#check Project.SpectralKL.Executable.kernel2_accepted
#check Project.SpectralKL.Executable.equalMoments_accepted_error
#print axioms Project.SpectralKL.Certificate.accepts_sound
#print axioms Project.SpectralKL.Certificate.Fast.certify
#print axioms Project.SpectralKL.Certificate.Fast.certify_score
#print axioms Project.SpectralKL.Certificate.Fast.accepted_error
#print axioms Project.SpectralKL.CertificateRun.wordValue_real
#print axioms Project.SpectralKL.Executable.kernel40_accepted
#print axioms Project.SpectralKL.Executable.kernel2_accepted
#print axioms Project.SpectralKL.Executable.equalMoments_accepted_error
