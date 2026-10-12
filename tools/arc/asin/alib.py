from fractions import Fraction as F
import math
u=F(1,2**53); eta=F(1,2**960); U=F(2)**-54
def val(b):
    s=b>>63; e=(b>>52)&0x7FF; f=b&((1<<52)-1)
    m=(f|(1<<52)) if e else f
    v=F(m)*F(2)**((e if e else 1)-1075)
    return -v if s else v
pS=[val(w) for w in [0x3FC5555555555555,0xBFD4D61203EB6F7D,0x3FC9C1550E884455,0xBFA48228B5688F3B,0x3F49EFE07501B288,0x3F023DE10DFDF709]]
qS=[F(1)]+[val(w) for w in [0xC0033A271C8A2D4B,0x40002AE59C598AC8,0xBFE6066C1B8D0159,0x3FB3B8C5B12E9282]]
def mul(a,b): return (a[0]*b[0], a[1]*b[0]+a[0]*b[1]+a[1]*b[1]+(a[0]+a[1])*(b[0]+b[1])*u+eta)
def add(a,b,M=None):
    M=a[0]+b[0] if M is None else M
    return (M, a[1]+b[1]+(M+a[1]+b[1])*u)
def div(a,b,mb):
    Ma,ea=a; eb=b[1]
    return (Ma/mb, (ea+Ma*eb/mb)/(mb-eb)+(Ma+ea)/(mb-eb)*u+eta)
def resc(a,k): return (a[0]*k,a[1]*k)
def Qmin(T):
    # min of Q(t) on [0,T] by sampling + margin
    m=min(sum(float(c)*(float(T)*i/2000)**k for k,c in enumerate(qS)) for i in range(2001))
    return F(m).limit_denominator(10000)-F(1,1000)
def ratio(T0):
    # t at scale σ_t (t ≤ T0), M=1
    t=(F(1),F(0))
    tk=resc(t,T0)              # scale 1
    acc=(abs(pS[5]),F(0))
    for i in range(4,-1,-1):
        acc=add((abs(pS[i]),F(0)),mul(tk,acc))
    p=mul(t,acc)               # scale σ_t
    accq=(abs(qS[4]),F(0))
    for i in range(3,0,-1):
        accq=add((abs(qS[i]),F(0)),mul(tk,accq))
    q=add((F(1),F(0)),mul(tk,accq))   # scale 1 (crude M)
    mq=Qmin(T0)
    r=div(p,q,mq)              # scale σ_t
    return p,q,mq,r

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

def hu(B):
    g=0
    while not (B < F(2)**(53+g)/F(2)**1074): g+=1
    return F(2)**g/2/F(2)**1074
def pmaxr(coeffs,lo,hi,N=2000):
    m=0.0
    for i in range(N+1):
        t=float(lo)+(float(hi)-float(lo))*i/N
        v=0.0
        for c in reversed(coeffs): v=float(c)+t*v
        m=max(m,abs(v))
    return F(m)*(1+F(1,10**6))
def pminr(coeffs,lo,hi,N=2000):
    m=1e9
    for i in range(N+1):
        t=float(lo)+(float(hi)-float(lo))*i/N
        v=0.0
        for c in reversed(coeffs): v=float(c)+t*v
        m=min(m,abs(v))
    return F(m)*(1-F(1,10**6))
# absolute-error chain with half-ulp everywhere on t in [lo,hi]
def mulA(a,b): 
    B=(a[0]+a[1])*(b[0]+b[1]); return (a[0]*b[0], a[1]*b[0]+a[0]*b[1]+a[1]*b[1]+hu(B)+F(1,2**1075))
def addA(a,b,M):
    e=a[1]+b[1]; return (M, e+hu(M+e))
def divA(a,b,mb):
    Ma,ea=a; eb=b[1]; B=(Ma+ea)/(mb-eb)
    return (Ma/mb,(ea+Ma*eb/mb)/(mb-eb)+hu(B)+F(1,2**1075))
def ratioA(lo,hi):
    t=(hi,F(0))
    acc=(abs(pS[5]),F(0))
    for i in range(4,-1,-1):
        pr=mulA(t,acc); pr=(pmaxr([F(0)]+pS[i+1:],lo,hi),pr[1])
        acc=addA((abs(pS[i]),F(0)),pr,pmaxr(pS[i:],lo,hi))
    p=mulA(t,acc); p=(pmaxr([F(0)]+pS,lo,hi),p[1])
    accq=(abs(qS[4]),F(0))
    for i in range(3,0,-1):
        pr=mulA(t,accq); pr=(pmaxr([F(0)]+qS[i+1:],lo,hi),pr[1])
        accq=addA((abs(qS[i]),F(0)),pr,pmaxr(qS[i:],lo,hi))
    pr=mulA(t,accq); pr=(pmaxr([F(0)]+qS[1:],lo,hi),pr[1])
    q=addA((F(1),F(0)),pr,pmaxr(qS,lo,hi))
    mq=pminr(qS,lo,hi)
    r=divA(p,q,mq)
    return p,q,mq,r
def a2b(xlo,xhi):
    lo=(1-xhi)/2; hi=(1-xlo)/2
    p,q,mq,r=ratioA(lo,hi)
    er=r[1]; Mr=r[0]
    smax=F(math.sqrt(float(hi)))*(1+F(1,10**9))
    es=hu(smax)
    e2sr = 2*smax*er + 2*es*Mr + hu(2*smax*Mr)
    Mc=smax*F(1,2**20); ec=4*u*Mc
    pio2_lo=val(0x3C91A62633145C07)
    Min=pio2_lo+2*Mc; ein=2*ec+hu(Min)
    Mp=2*smax*Mr+Min; ep=e2sr+ein+hu(Mp)
    smin=F(math.sqrt(float(lo)))
    pio4=val(0x3FE921FB54442D18)
    Mq=max(abs(pio4-2*smin),abs(pio4-2*smax)); eq=hu(Mq)
    Mpq=Mp+Mq; epq=ep+eq+hu(Mpq)
    ker=2*smax**3*F(11,16)/F(2)**56
    tot=epq+ker+F(1,2**80)
    return float(tot/U), math.asin(float(xlo)), float(er/U)

