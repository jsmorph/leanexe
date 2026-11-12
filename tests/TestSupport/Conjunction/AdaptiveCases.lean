import Demos.Conjunction.Adaptive
import TestSupport.Conjunction.AccuracyCases
import TestSupport.Conjunction.Cases

/-! Cases of the module `adaptive`.  `cases` prints the module cases of `pcAdaptive` and
`circularErrorAdaptive` for `tests/verified/run.sh`.  `bits` prints the lines that
`tests/conjunction/accuracy.py` checks: `probability m1 m2 c11 c12 c22 r n status lo hi` for
`pcAdaptive`, with the tag `probability-thin` for an input whose reference is a bracket and
`probability-rejected` for an input that must be rejected, and `adaptive m1 m2 c11 c12 c22 p n k
status lo hi` for `circularErrorAdaptive`, with the tag `adaptive-small` for few panels, where status
2 is allowed, and `adaptive-rejected` for an input that must be rejected.  `sweep` prints, for each
input and probability of `sweepDisks` and each of `circularError` and `circularErrorAdaptive`, the
least panel count of `16, 32, ..., 1048576` at which the search returns status 0 and the least at
which it also returns an interval at most a hundredth of `lo` wide, as a line
`sweep method n0 n1` with the input, followed by the results at those counts as lines
`circular-at` or `adaptive-at` with the fields of `adaptive`. -/

namespace TestSupport.Conjunction.AdaptiveCases

open TestSupport.Host Demos.Conjunction.Adaptive
open TestSupport.Conjunction.AccuracyCases (disks probabilities diskRejected)

/-- Means and covariances with biases of 10, 100, and 1,000 standard deviations along each axis,
and an elongated covariance with a bias of 30 standard deviations of the smaller variance. -/
def farDisks : List (Float × Float × Float × Float × Float) :=
  [ (10, 0, 1, 0, 1), (0, 10, 1, 0, 1), (100, 0, 1, 0, 1), (0, 100, 1, 0, 1),
    (1000, 0, 1, 0, 1), (0, 1000, 1, 0, 1), (0, 30, 100, 0, 1) ]

/-- Inputs of the sweep: centered, biased by 3 standard deviations along each axis, the far
inputs, and the correlated sample. -/
def sweepDisks : List (Float × Float × Float × Float × Float) :=
  [(0, 0, 1, 0, 1), (3, 0, 1, 0, 1), (0, 3, 1, 0, 1)] ++ farDisks ++ [(2, -1, 25, 6, 16)]

/-- Inputs that `pcAdaptive` rejects: those of the conjunction cases and an input whose panels
overflow, on which a common part that took a stopped march's sum would miss the probability. -/
def probabilityRejected : List (Float × Float × Float × Float × Float × Float) :=
  TestSupport.Conjunction.Cases.rejected ++ [(-1.3e154, 0, 2e307, 0, 2e307, 1.3e154)]

/-- An input on which the marches accept panels for their length: the first variance is `1e-28`,
so the exponential factor varies on a scale below `r · 2^-40`. -/
def thinInputs : List (Float × Float × Float × Float × Float × Float) :=
  [(0, 0, 1e-28, 0, 1, 1)]

/-- Inputs whose search ends with status 2 at the panels given. -/
def adaptiveUnfinished : List (Float × Float × Float × Float × Float × Float × UInt64 × UInt64) :=
  [ (0, 0, 1, 0, 1, 0.9999999, 256, 4), (0, 0, 1, 0, 1, 0.999999, 1024, 4),
    (0, 0, 1, 0, 1, 0.99, 16, 4) ]

def probabilityLine (m1 m2 c11 c12 c22 r : Float) (n : UInt64) : IO Unit :=
  let p := pcAdaptive m1 m2 c11 c12 c22 r n
  line "adaptive" "pcAdaptive" "list:i64,f64,f64"
    [fl m1, fl m2, fl c11, fl c12, fl c22, fl r, u n]
    s!"{p.status} {p.lo.toBits} {p.hi.toBits}"

def diskLine (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : IO Unit :=
  let r := circularErrorAdaptive m1 m2 c11 c12 c22 p n k
  line "adaptive" "circularErrorAdaptive" "list:i64,f64,f64"
    [fl m1, fl m2, fl c11, fl c12, fl c22, fl p, u n, u k]
    s!"{r.status} {r.lo.toBits} {r.hi.toBits}"

def cases : IO Unit := do
  for (m1, m2, c11, c12, c22, r) in
      TestSupport.Conjunction.Cases.inputs ++ thinInputs ++ probabilityRejected do
    for n in [(15 : UInt64), 16, 64, 100, 256, 1048577] do
      probabilityLine m1 m2 c11 c12 c22 r n
  for (m1, m2, c11, c12, c22) in disks ++ farDisks do
    for p in [0.9, 0.99] do
      for n in [(16 : UInt64), 256] do
        for k in [(0 : UInt64), 20] do
          diskLine m1 m2 c11 c12 c22 p n k
  for (m1, m2, c11, c12, c22, p, n, k) in diskRejected do
    diskLine m1 m2 c11 c12 c22 p (if n == 16 then 64 else n) k
  for (m1, m2, c11, c12, c22, p, n, k) in adaptiveUnfinished ++ [(0, 0, 1, 0, 1, 0.9, 15, 4)] do
    diskLine m1 m2 c11 c12 c22 p n k

def probabilityBits (tag : String) (m1 m2 c11 c12 c22 r : Float) (n : UInt64) : IO Unit := do
  let p := pcAdaptive m1 m2 c11 c12 c22 r n
  IO.println s!"{tag} {m1.toBits} {m2.toBits} {c11.toBits} {c12.toBits} {c22.toBits} {r.toBits} {n} {p.status} {p.lo.toBits} {p.hi.toBits}"

def radiusBits (tag : String) (r : Demos.Conjunction.Accuracy.Radius)
    (m1 m2 c11 c12 c22 p : Float) (n k : UInt64) : IO Unit :=
  IO.println s!"{tag} {m1.toBits} {m2.toBits} {c11.toBits} {c12.toBits} {c22.toBits} {p.toBits} {n} {k} {r.status} {r.lo.toBits} {r.hi.toBits}"

def bits : IO Unit := do
  for (m1, m2, c11, c12, c22, r) in TestSupport.Conjunction.Cases.inputs do
    for n in [(16 : UInt64), 100, 256, 4096] do
      probabilityBits "probability" m1 m2 c11 c12 c22 r n
  for (m1, m2, c11, c12, c22, r) in thinInputs do
    for n in [(16 : UInt64), 100, 256, 4096] do
      probabilityBits "probability-thin" m1 m2 c11 c12 c22 r n
  for (m1, m2, c11, c12, c22, r) in probabilityRejected do
    probabilityBits "probability-rejected" m1 m2 c11 c12 c22 r 256
  for n in [(0 : UInt64), 15, 1048577] do
    probabilityBits "probability-rejected" 300 0 10000 0 1000000 20 n
  for (m1, m2, c11, c12, c22) in disks ++ farDisks do
    for p in probabilities do
      for n in (if p == 0.99 then [(4096 : UInt64), 65536] else [256, 4096, 65536]) do
        radiusBits "adaptive" (circularErrorAdaptive m1 m2 c11 c12 c22 p n 30)
          m1 m2 c11 c12 c22 p n 30
      for n in [(32 : UInt64), 64, 128] do
        radiusBits "adaptive-small" (circularErrorAdaptive m1 m2 c11 c12 c22 p n 30)
          m1 m2 c11 c12 c22 p n 30
  for (m1, m2, c11, c12, c22, p, n, k) in adaptiveUnfinished do
    radiusBits "adaptive" (circularErrorAdaptive m1 m2 c11 c12 c22 p n k) m1 m2 c11 c12 c22 p n k
  for (m1, m2, c11, c12, c22, p, n, k) in diskRejected ++ [(0, 0, 1, 0, 1, 0.9, 15, 4)] do
    let n := if n == 16 then 64 else n
    radiusBits "adaptive-rejected" (circularErrorAdaptive m1 m2 c11 c12 c22 p n k)
      m1 m2 c11 c12 c22 p n k

/-- The least panel count of `16, 32, ..., 1048576` at which `search` returns status 0, and the
least at which it returns status 0 with `hi - lo ≤ lo / 100`, each with its result, or 0. -/
def leastPanels (search : UInt64 → Demos.Conjunction.Accuracy.Radius) :
    (UInt64 × Demos.Conjunction.Accuracy.Radius) ×
      (UInt64 × Demos.Conjunction.Accuracy.Radius) := Id.run do
  let mut n : UInt64 := 16
  let mut first : UInt64 × Demos.Conjunction.Accuracy.Radius := (0, ⟨2, 0, 0⟩)
  while n ≤ 1048576 do
    let r := search n
    if r.status == 0 then
      if first.1 == 0 then first := (n, r)
      if r.hi - r.lo ≤ 0.01 * r.lo then return (first, (n, r))
    n := 2 * n
  return (first, (0, ⟨2, 0, 0⟩))

def sweep : IO Unit := do
  for (m1, m2, c11, c12, c22) in sweepDisks do
    for p in probabilities do
      for (tag, search) in
          [("circular", fun n => Demos.Conjunction.Accuracy.circularError m1 m2 c11 c12 c22 p n 30),
           ("adaptive", fun n => circularErrorAdaptive m1 m2 c11 c12 c22 p n 30)] do
        let ((n0, r0), (n1, r1)) := leastPanels search
        IO.println s!"sweep {tag} {n0} {n1} m=({m1},{m2}) C=({c11},{c12},{c22}) p={p}"
        if n0 != 0 then radiusBits s!"{tag}-at" r0 m1 m2 c11 c12 c22 p n0 30
        if n1 != 0 && n1 != n0 then radiusBits s!"{tag}-at" r1 m1 m2 c11 c12 c22 p n1 30

end TestSupport.Conjunction.AdaptiveCases
