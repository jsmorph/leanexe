import CodeLib.IEEE64.Roundoff

namespace Project.TinyGpt2.ErrorBudget
open CodeLib.IEEE64

noncomputable def embedding (bound : ℝ) : ℝ := (2*bound+1)*arithmeticEpsilon

noncomputable def normalization (inputBound bound error lower : ℝ) : ℝ :=
  (16000*bound*inputBound+254*bound+2)*arithmeticEpsilon+bound*(2*error/lower)

noncomputable def column4 (inputBound bound error : ℝ) : ℝ :=
  (12*(inputBound*bound+1)+6)*arithmeticEpsilon+4*bound*error

noncomputable def column8 (inputBound bound error : ℝ) : ℝ :=
  (32*(inputBound*bound+1)+22)*arithmeticEpsilon+8*bound*error

noncomputable def normalizedEmbedding (bound lower1 : ℝ) : ℝ :=
  normalization 21 bound (embedding bound) lower1

noncomputable def projection (bound lower1 : ℝ) : ℝ :=
  column4 31 bound (normalizedEmbedding bound lower1)

noncomputable def projectionMagnitude (bound : ℝ) : ℝ := 12*bound^2+1

noncomputable def score (bound lower1 : ℝ) : ℝ :=
  (16*(projectionMagnitude bound)^2+3)*arithmeticEpsilon+
    2*(projectionMagnitude bound+12*bound^2)*(projection bound lower1)

noncomputable def attention (bound lower1 : ℝ) : ℝ :=
  (10077*projectionMagnitude bound+6)*arithmeticEpsilon+
    2*projectionMagnitude bound*(score bound lower1)+projection bound lower1

noncomputable def residual1 (bound lower1 : ℝ) : ℝ :=
  50041*arithmeticEpsilon+embedding bound+
    (50019*arithmeticEpsilon+column4 1250 bound (attention bound lower1))

noncomputable def expanded (bound lower1 lower2 : ℝ) : ℝ :=
  1259*arithmeticEpsilon+
    column4 31 bound (normalization 60000 bound (residual1 bound lower1) lower2)

noncomputable def activated (bound lower1 lower2 : ℝ) : ℝ :=
  200000*arithmeticEpsilon+4*expanded bound lower1 lower2

noncomputable def contracted (bound lower1 lower2 : ℝ) : ℝ :=
  100909*arithmeticEpsilon+column8 1261 bound (activated bound lower1 lower2)

noncomputable def residual2 (bound lower1 lower2 : ℝ) : ℝ :=
  160910*arithmeticEpsilon+residual1 bound lower1+contracted bound lower1 lower2

noncomputable def hidden (bound lower1 lower2 lowerFinal : ℝ) : ℝ :=
  normalization 200000 bound (residual2 bound lower1 lower2) lowerFinal

noncomputable def logits (bound lower1 lower2 lowerFinal : ℝ) : ℝ :=
  1259*arithmeticEpsilon+column4 31 bound (hidden bound lower1 lower2 lowerFinal)

end Project.TinyGpt2.ErrorBudget
