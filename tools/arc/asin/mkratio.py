# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
exec(open('genratio.py').read().split('if __name__')[0])
head='''import Library.Numerics.Float64.Asin.AsinTheoremSupport

/-!
The rational function of `Asin.asinRatio`, `t (pS0 + ... + pS5 t ^ 5)/(1 + qS1 t + ... + qS4 t ^ 4)`
in the order of `e_asin.c`, as `F64Approx.SApprox` chains for seven ranges of `t`.  Each partial
sum of the two Horner schemes has a bound over its range that the kernel checks with
`PolyBound.check`, which keeps the bounds near the true magnitudes of the alternating sums, and
the denominator's lower bound comes from the same check.  The input `t` may carry a relative
error, as `x * x` does.
-/

namespace Library.Numerics.Float64.Asin.AsinTheoremRatio
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx PolyBound AsinTheoremSupport

set_option exponentiation.threshold 4096

'''
body=head
res={}
for name,lo,hi,etk,slo in [("S1",F(0),F(1,8),F(10001,10000),54),("S2",F(1,8),F(1,4),F(10001,10000),54),
                           ("A1",F(1,5),F(1,4),F(0),54),("A2",F(1,20),F(1,5),F(0),54),
                           ("A3",F(1,80),F(1,20),F(0),54),("A4",F(0),F(1,79),F(0),56),("W",F(0),F(1,4),F(0),56)]:
    txt,r,mq=theorem(name,lo,hi,etk,slo)
    body+=txt+"\n"
    res[name]=(r,mq)
    print(name,float(lo),float(hi),"Mr",r[0],"er/u",r[1]/u,float(r[1]/u),"mq",float(mq))
body+="end Library.Numerics.Float64.Asin.AsinTheoremRatio\n"
open('../AsinTheoremRatio.lean','w').write(body)
