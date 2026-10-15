# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
from fractions import Fraction as F
import math
exec(open('genratio.py').read().split('if __name__')[0])
def hu(B):
    g=0
    while not (B < F(2)**(53+g)/F(2)**1074): g+=1
    return g, F(2)**g/2/F(2)**1074
def upq(x,den=10**6): return F(math.ceil(x*den),den)
def dnq(x,den=10**6): return F(math.floor(x*den),den)
vlo=val(0x3C91A62633145C07); vh4=val(0x3FE921FB54442D18)
kap=F(11,16)/F(2)**56
def plan(alo,ahi,chain,n):
    lo=(1-ahi)/2; hi=(1-alo)/2
    shi=upq(F(math.sqrt(float(hi)))*(1+F(1,10**9)))
    slo=dnq(F(math.sqrt(float(lo)))*(1-F(1,10**9)))
    g,r,mq=gen(chain[0],chain[1],chain[2],F(0),56)
    Mr,er=r[0],r[1]
    es=shi*u
    Mtw=upq(hi*(F(1,2**19)*F(101,100))+4*es*shi,10**12)
    vwlo=(slo-es)*(1-F(1,2**20)); vwhi=shi+es
    Bsw=2*(shi+es); esw=Bsw*u
    mb=dnq(2*vwlo,10**6)
    Mc=upq(Mtw/mb,10**12)
    ec=(0+Mtw*esw/mb)/(mb-esw)+(Mtw/(mb-esw))*u+F(1,2**1075)
    Bc2=2*(Mc+ec); ec2=2*ec+Bc2*u+F(1,2**1075)
    Blo=upq(abs(vlo)+2*Mc+ec2,10**12); elo=ec2+Blo*u
    MrA=Mr*hi; erA=er*hi
    Bsr=(2*shi+2*es)*(MrA+erA); esr=2*es*MrA+2*shi*erA+2*es*erA+Bsr*u+F(1,2**1075)
    Mp=2*shi*MrA+Blo
    gp,hp=hu(Mp+esr+elo); ep=esr+elo+hp
    Mq=max(abs(vh4-2*vwlo),abs(vh4-2*vwhi))
    gq,hq=hu(Mq); eq=hq
    Mpq=Mp+Mq
    gpq,hpq=hu(Mpq+ep+eq); epq=ep+eq+hpq
    mbp=dnq(slo+vwlo,10**6)
    small=Mtw*es/(mbp*mb)
    E=epq+F(1,2**64)+2*shi**3*kap+2*small
    h=F(2)**(n-1)/F(2)**1074
    return dict(lo=lo,hi=hi,shi=shi,slo=slo,Mr=Mr,er=er,Mtw=Mtw,mb=mb,Mc=Mc,Blo=Blo,gp=gp,gq=gq,gpq=gpq,E=E,h=h,Mq=Mq,Mp=Mp,mbp=mbp)
for alo,ahi,ch,n in [(F(1,2),F(6,10),("A1",F(1,5),F(1,4)),1022),(F(6,10),F(9,10),("A2",F(1,20),F(1,5)),1022),(F(9,10),F(975,1000),("A3",F(1,80),F(1,20)),1023)]:
    d=plan(alo,ahi,ch,n)
    print(float(alo),float(ahi),"E/2^-54=%.3f limit=%.3f"%(float(d['E']/F(2)**-54),float(d['h']/F(2)**-54)),"g",d['gp'],d['gq'],d['gpq'])
U=F(2)**-54
alo,ahi=F(1,2),F(6,10); lo=(1-ahi)/2; hi=(1-alo)/2
g,r,mq=gen("A1",F(1,5),F(1,4),F(0),56)
print("chain Mr",float(r[0]),"er/u",float(r[1]/u),"MrA",float(r[0]*hi),"erA units",float(r[1]*hi/U))
shi=F(1,2); es=shi*u
print("2shi*erA units",float(2*shi*r[1]*hi/U),"2es*MrA units",float(2*es*r[0]*hi/U))
