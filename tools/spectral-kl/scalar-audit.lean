import Project.SpectralKL.ScalarEstimator

-- Input assumptions and exact mathematical target.
#print Project.SpectralKL.Scalar.ValidSamples
#print Project.SpectralKL.Scalar.ValidRidge
#print Project.SpectralKL.Scalar.exactMean
#print Project.SpectralKL.Scalar.exactSecond
#print Project.SpectralKL.Scalar.regularizedIntegral

-- Executed source and the universally quantified numerical theorem.
#print LeanExe.Examples.SpectralKL.fromBoundedSamples
#print LeanExe.Examples.SpectralKL.scalarStats
#print LeanExe.Examples.SpectralKL.scalarScore
#check Project.SpectralKL.Scalar.fromBoundedSamples_correct
#print axioms Project.SpectralKL.Scalar.fromBoundedSamples_correct
#check Project.SpectralKL.Scalar.fromUnitSamples_correct
#print axioms Project.SpectralKL.Scalar.fromUnitSamples_correct

-- Source/model connection for the arithmetic and reduction steps.
#check Project.SpectralKL.Scalar.sampleSum_model
#check Project.SpectralKL.Scalar.sampleSquares_model
#check Project.SpectralKL.Scalar.sampleCount_model
#check Project.SpectralKL.Executable.kernel40_model
#check Project.SpectralKL.Operations.add
#check Project.SpectralKL.Operations.sub
#check Project.SpectralKL.Operations.mul
#check Project.SpectralKL.Operations.div
