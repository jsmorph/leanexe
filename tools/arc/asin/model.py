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
for T0 in [F(1,4),F(1,8),F(1,32)]:
    p,q,mq,r=ratio(T0)
    print("T0",float(T0),"mq",float(mq),"r M",float(r[0]),"e/u",float(r[1]/u))
