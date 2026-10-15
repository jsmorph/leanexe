# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
exec(open("lib.py").read())
def hu(B):
    g=0
    while not (B < F(2)**(53+g)/F(2)**1074): g+=1
    return F(2)**g/2/F(2)**1074
def ratio_range(Tlo,Thi):
    # absolute errors for t in [Tlo,Thi], t exact input
    p,q,mq,r=ratio_tight(Thi)
    # r error at scale σ_t=t <= Thi
    return r
# A2b: |x| in [xlo,xhi], t=(1-|x|)/2 in [(1-xhi)/2,(1-xlo)/2]
def a2b(xlo,xhi):
    Tlo=(1-xhi)/2; Thi=(1-xlo)/2
    r=ratio_tight(Thi)[3]
    er=r[1]*Thi            # absolute error of r
    Mr=r[0]*Thi
    smax=F(math.sqrt(float(Thi)))*(1+F(1,10**9))
    es=hu(smax)            # sqrt rounding
    # 2s*r: 2s exact; product
    e2sr = 2*smax*er + 2*es*Mr + hu(2*smax*Mr)
    # c ~ small: (t-w^2)/(s+w): magnitude <= 2^-20 * s ; error relative u*|c|*3
    Mc=smax*F(1,2**20); ec=3*u*Mc
    # p = 2s*r - (pio2_lo - 2c): inner pio2_lo-2c magnitude ~6e-17+..., error 2ec + hu
    pio2_lo=val(0x3C91A62633145C07)
    Min=pio2_lo+2*Mc; ein=2*ec+hu(Min)
    Mp=2*smax*Mr+Min; ep=e2sr+ein+hu(Mp)
    # q = pio4_hi - 2w: |q| <= max(|0.785-2*smin|,|0.785-2*smax|)
    smin=F(math.sqrt(float(Tlo)))
    pio4=val(0x3FE921FB54442D18)
    Mq=max(abs(pio4-2*smin),abs(pio4-2*smax)); eq=hu(Mq)
    # p - q
    Mpq=Mp+Mq; epq=ep+eq+hu(Mpq)
    # kernel: 2*sqrt(t)^3*(11/16)/2^56 ; sqrt vs s in 2*s*r uses s, mismatch: exact formula uses sqrt(t): 2|s-sqrt t|*R
    ker=2*smax**3*F(11,16)/F(2)**56
    tot=epq+ker+F(1,2**80)
    ylo=F(math.asin(float(xlo))); 
    return float(tot/U), float(ylo)
for xlo,xhi in [(F(1,2),F(975,1000)),(F(1,2),F(6,10)),(F(6,10),F(7,10)),(F(7,10),F(975,1000)),(F(1,2),F(55,100))]:
    print(float(xlo),float(xhi),"E/2^-54=%.3f y>=%.4f"%a2b(xlo,xhi))
xlo,xhi=F(1,2),F(55,100)
Tlo=(1-xhi)/2; Thi=(1-xlo)/2
p,q,mq,r=ratio_tight(Thi)
print("p M e/u",float(p[0]),float(p[1]/u),"q M e/u",float(q[0]),float(q[1]/u),"mq",float(mq),"r e/u",float(r[1]/u))
er=r[1]*Thi; Mr=r[0]*Thi
print("abs r err units",float(er/U),"Mr",float(Mr))
