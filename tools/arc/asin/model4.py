# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
exec(open("lib.py").read())
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
for xlo,xhi in [(F(1,2),F(55,100)),(F(55,100),F(6,10)),(F(6,10),F(7,10)),(F(7,10),F(8,10)),(F(8,10),F(9,10)),(F(9,10),F(975,1000)),(F(1,2),F(6,10)),(F(6,10),F(975,1000))]:
    print(float(xlo),float(xhi),"E/2^-54=%.3f y>=%.4f  r err=%.3f"%a2b(xlo,xhi))
