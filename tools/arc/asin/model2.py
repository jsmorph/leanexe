# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
exec(open('model.py').read().split("for T0 in")[0])
def pmax(coeffs,T0,N=4000):
    # max |sum c_k t^k| on [0,T0] sampled, plus margin
    m=0.0
    for i in range(N+1):
        t=float(T0)*i/N
        v=0.0
        for c in reversed(coeffs): v=float(c)+t*v
        m=max(m,abs(v))
    return F(m)*(1+F(1,10**6))
def ratio_tight(T0):
    t=(F(1),F(0))
    tk=resc(t,T0)
    # Horner for P: partial polys
    acc=(abs(pS[5]),F(0)); 
    for i in range(4,-1,-1):
        pr=mul(tk,acc)
        # tight bound on product value: |t * partial_{i+1}(t)| <= T0 * max|partial_{i+1}|... use pmax of t*poly
        part=pS[i+1:]
        Mprod=pmax([F(0)]+part,T0)
        pr=(min(pr[0],Mprod),pr[1])
        acc=add((abs(pS[i]),F(0)),pr,M=pmax(pS[i:],T0))
    p=mul(t,acc)
    accq=(abs(qS[4]),F(0))
    for i in range(3,0,-1):
        pr=mul(tk,accq); pr=(min(pr[0],pmax([F(0)]+qS[i+1:],T0)),pr[1])
        accq=add((abs(qS[i]),F(0)),pr,M=pmax(qS[i:],T0))
    pr=mul(tk,accq); pr=(min(pr[0],pmax([F(0)]+qS[1:],T0)),pr[1])
    q=add((F(1),F(0)),pr,M=pmax(qS,T0))
    mq=Qmin(T0)
    r=div(p,q,mq)
    return p,q,mq,r
for T0 in [F(1,4),F(1,8),F(1,16),F(1,32)]:
    p,q,mq,r=ratio_tight(T0)
    # asin small branch: x + x*r(x^2): relative to |x|: e_r * t (t<=T0) plus rounding of x*r
    xr=( r[0]*T0, (r[1]*T0 + r[0]*T0*u) )   # relative to |x| scale
    print("T0",float(T0),"r M",float(r[0]),"e/u",float(r[1]/u),"  x*r rel err/u",float(xr[1]/u))
