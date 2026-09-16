import Project.TinyGpt2.Model
import Mathlib.Tactic

namespace Project.TinyGpt2Hidden.Spec
open Project.TinyGpt2

theorem hidden_of_stages (weights : Array UInt64) (t0 t1 t2 t3 position : UInt64)
    {e0 e1 e2 e3 n0 n1 n2 n3 queryRow query attended projected attentionBias embeddedRow residual nff lowBias highBias actLow actHigh contracted : Row}
    {keys values : Context} {d0 d1 d2 d3 d4 d5 d6 d7 : UInt64}
    (he0 : embedding weights t0 0 = e0)
    (he1 : embedding weights t1 1 = e1)
    (he2 : embedding weights t2 2 = e2)
    (he3 : embedding weights t3 3 = e3)
    (hn0 : Project.TinyGpt2.norm weights 2464 e0 = n0)
    (hn1 : Project.TinyGpt2.norm weights 2464 e1 = n1)
    (hn2 : Project.TinyGpt2.norm weights 2464 e2 = n2)
    (hn3 : Project.TinyGpt2.norm weights 2464 e3 = n3)
    (hqueryRow : contextRow ⟨n0, n1, n2, n3⟩ position = queryRow)
    (hquery : project4 weights 1040 queryRow = query)
    (hkeys : projectContext weights 1056 ⟨n0, n1, n2, n3⟩ = keys)
    (hvalues : projectContext weights 1072 ⟨n0, n1, n2, n3⟩ = values)
    (hattended : attentionRow (position+1) query keys values = attended)
    (hprojected : project4 weights 1088 attended = projected)
    (habias : loadRow weights 1104 = attentionBias)
    (hembeddedRow : contextRow ⟨e0, e1, e2, e3⟩ position = embeddedRow)
    (hresidual : addRows embeddedRow (addRows projected attentionBias) = residual)
    (hnff : Project.TinyGpt2.norm weights 2472 residual = nff)
    (hd0 : dotColumn4 weights 1108 8 0 nff = d0)
    (hd1 : dotColumn4 weights 1108 8 1 nff = d1)
    (hd2 : dotColumn4 weights 1108 8 2 nff = d2)
    (hd3 : dotColumn4 weights 1108 8 3 nff = d3)
    (hd4 : dotColumn4 weights 1108 8 4 nff = d4)
    (hd5 : dotColumn4 weights 1108 8 5 nff = d5)
    (hd6 : dotColumn4 weights 1108 8 6 nff = d6)
    (hd7 : dotColumn4 weights 1108 8 7 nff = d7)
    (hlbias : loadRow weights 1140 = lowBias)
    (hhbias : loadRow weights 1144 = highBias)
    (hactLow : activate (addRows ⟨d0, d1, d2, d3⟩ lowBias) = actLow)
    (hactHigh : activate (addRows ⟨d4, d5, d6, d7⟩ highBias) = actHigh)
    (hcontracted : contractRow weights ⟨actLow, actHigh⟩ = contracted)
    : Project.TinyGpt2.hidden weights t0 t1 t2 t3 position =
      Project.TinyGpt2.norm weights 2480 (addRows residual contracted) := by
  simp only [Project.TinyGpt2.hidden, expandRow, Layout.norm1, Layout.norm2, Layout.normFinal,
    Layout.query, Layout.key, Layout.value, Layout.attention, Layout.attentionBias,
    Layout.expand, Layout.expandBias, he0, he1, he2, he3, hn0, hn1, hn2, hn3, hqueryRow, hquery, hkeys, hvalues, hattended, hprojected, habias, hembeddedRow, hresidual, hnff, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, hlbias, hhbias, hactLow, hactHigh, hcontracted]

#print axioms hidden_of_stages
end Project.TinyGpt2Hidden.Spec
