from fractions import Fraction as F
import math
u=F(1,2**53); eta=F(1,2**960)
def val(b):
    s=b>>63; e=(b>>52)&0x7FF; f=b&((1<<52)-1)
    m=(f|(1<<52)) if e else f
    v=F(m)*F(2)**((e if e else 1)-1075)
    return -v if s else v
PW=[0x3FC5555555555555,0xBFD4D61203EB6F7D,0x3FC9C1550E884455,0xBFA48228B5688F3B,0x3F49EFE07501B288,0x3F023DE10DFDF709]
QW=[None,0xC0033A271C8A2D4B,0x40002AE59C598AC8,0xBFE6066C1B8D0159,0x3FB3B8C5B12E9282]
pS=[val(w) for w in PW]; qS=[F(1)]+[val(w) for w in QW[1:]]
def up(x,den): return F(math.ceil(x*den),den)
def dn(x,den): return F(math.floor(x*den),den)
def upM(x):
    if x==0: return F(0)
    if x>F(1,100): return up(x,10000)
    return up(x,10**8)
def fmtq(q):
    if q<0: return f"(-{fmtq(-q)})"
    return f"({q.numerator} / {q.denominator})" if q.denominator!=1 else f"{q.numerator}"
def eu(e): return up(e/u,10000)
def fmte(k): return f"{fmtq(k)} / 2 ^ 53"
def iabs(iv): return max(abs(iv[0]),abs(iv[1]))
def srange(coeffs,lo,hi,N=4000):
    vals=[]
    for i in range(N+1):
        t=float(lo)+(float(hi)-float(lo))*i/N
        v=0.0
        for c in reversed(coeffs): v=float(c)+t*v
        vals.append(v)
    L=F(min(vals)); U=F(max(vals)); m=(U-L)*F(1,1000)+F(1,10**7)
    return (L-m,U+m)
def ihorner(coeffs,lo,hi):
    return {i:srange(coeffs[i:],lo,hi) for i in range(len(coeffs))}
def exprP(j):
    if j==5: return f"value 0x{PW[5]:016X}"
    return f"(value 0x{PW[j]:016X} + vt * {exprP(j+1)})"
def exprQ(j):
    if j==4: return f"value 0x{QW[4]:016X}"
    return f"(value 0x{QW[j]:016X} + vt * {exprQ(j+1)})"
class G:
    def __init__(s): s.L=[]
    def e(s,l): s.L.append(l)
    def mono(s,name,expr,M,e):
        Mr=upM(M); k=eu(e)
        s.e(f"  have {name} := ({expr}).mono")
        s.e(f"    (M' := {fmtq(Mr)}) (e' := {fmte(k)}) (by norm_num) (by norm_num)")
        return (Mr,k*u)
    def const(s,name,w,v):
        Mr=upM(abs(v))
        s.e(f"  have {name} := fsapprox_const 0x{w:016X} (by decide +kernel) (({fmtq(Mr)} : ℚ) : ℝ)")
        s.e(f"    (abs_value_le _ _ (by decide +kernel))")
        return (Mr,F(0))
    def mul(s,name,a,an,b,bn,heta):
        M=a[0]*b[0]; e=a[1]*b[0]+a[0]*b[1]+a[1]*b[1]+(a[0]+a[1])*(b[0]+b[1])*u+eta
        return s.mono(name,f"fsapprox_mul {an} {bn} (1 / 2 ^ 960) {heta} (by norm_num)",M,e)
    def addM(s,name,a,an,b,bn,M,hb):
        e=a[1]+b[1]+(M+(a[1]+b[1]))*u
        return s.mono(name,f"fsapprox_add {an} {bn} {fmtq(M)} {hb} (by norm_num)",M,e)
    def bound(s,name,words,expr,lo,hi,M,first=None):
        lst=", ".join((f"ratOfWord 0x{w:016X}" if w is not None else fmtq(first)) for w in words)
        s.e(f"  have {name} : |{expr}| ≤ {fmtq(M)} * 1 := by")
        s.e(f"    have h := poly_bound [{lst}] {fmtq(lo)} {fmtq(hi)} {fmtq(M)} 12 (by decide +kernel) vt")
        s.e(f"      (by push_cast; linarith) (by push_cast; linarith)")
        s.e(f"    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h")
        s.e(f"    rw [mul_one]; push_cast at h; exact h")
def gen(name,lo,hi,etk,slo):
    g=G(); et=etk*u
    t=(F(1),et)
    tk=g.mono("tk",f"ht.rescale 1 {fmtq(hi)} one_pos le_rfl hk1",hi,et*hi)
    ip=ihorner(pS,lo,hi); iq=ihorner(qS,lo,hi)
    acc=g.const("c5",PW[5],pS[5]); accn="c5"
    for i in range(4,-1,-1):
        pr=g.mul(f"pr{i}",tk,"tk",acc,accn,"hη1")
        g.e(f"  have pq{i} := pr{i}.rescale 1 1 one_pos le_rfl (by norm_num)")
        c=g.const(f"c{i}",PW[i],pS[i])
        Mi=upM(iabs(ip[i])*(1+F(1,10**6)))
        g.bound(f"hb{i}",PW[i:],f"value 0x{PW[i]:016X} + vt * {exprP(i+1)}",lo,hi,Mi)
        acc=g.addM(f"a{i}",c,f"c{i}",pr,f"pq{i}",Mi,f"hb{i}"); accn=f"a{i}"
    p=g.mul("p0",t,"ht",acc,"a0","hησ")
    g.e("  have p1 := p0.rescale σ 1 hσp hσ1 (by rw [mul_one, one_mul])")
    accq=g.const("d4",QW[4],qS[4]); accqn="d4"
    for i in range(3,0,-1):
        pr=g.mul(f"qr{i}",tk,"tk",accq,accqn,"hη1")
        g.e(f"  have qq{i} := qr{i}.rescale 1 1 one_pos le_rfl (by norm_num)")
        c=g.const(f"d{i}c",QW[i],qS[i])
        Mi=upM(iabs(iq[i])*(1+F(1,10**6)))
        g.bound(f"hq{i}",QW[i:],f"value 0x{QW[i]:016X} + vt * {exprQ(i+1)}",lo,hi,Mi)
        accq=g.addM(f"d{i}",c,f"d{i}c",pr,f"qq{i}",Mi,f"hq{i}"); accqn=f"d{i}"
    pr=g.mul("qr0",tk,"tk",accq,accqn,"hη1")
    g.e("  have qq0 := qr0.rescale 1 1 one_pos le_rfl (by norm_num)")
    MQ=upM(iabs(iq[0])*(1+F(1,10**6)))
    g.bound("hq0",[None]+QW[1:],f"1 + vt * {exprQ(1)}",lo,hi,MQ,first=F(1))
    q=g.addM("q0",(F(1),F(0)),"one1",pr,"qq0",MQ,"hq0")
    # lower bound of Q
    Lq=iq[0][0]; c=(Lq+iq[0][1])/2; eps=(iq[0][1]-Lq)/2*(1+F(1,10**6))
    cq=dn(c,10**6); epsq=up(eps+abs(c-cq),10**6)
    mq=cq-epsq
    lst=", ".join([fmtq(1-cq)]+[f"ratOfWord 0x{w:016X}" for w in QW[1:]])
    g.e(f"  have hmq : {fmtq(mq)} ≤ |1 + vt * {exprQ(1)}| := by")
    g.e(f"    have h := poly_bound [{lst}] {fmtq(lo)} {fmtq(hi)} {fmtq(epsq)} 12 (by decide +kernel) vt")
    g.e(f"      (by push_cast; linarith) (by push_cast; linarith)")
    g.e(f"    simp only [eval_cons, eval_nil, mul_zero, add_zero, ratOfWord_cast] at h")
    g.e(f"    push_cast at h")
    g.e(f"    have h2 := (abs_le.mp h).1")
    g.e(f"    rw [abs_of_pos (by norm_num at h2 ⊢; linarith)]")
    g.e(f"    norm_num at h2 ⊢; linarith")
    Ma,ea=(acc[0],p[1]); eb=q[1]
    M=Ma/mq; e=(ea+Ma*eb/mq)/(mq-eb)+(Ma+ea)/(mq-eb)*u+eta
    r=g.mono("r0",f"fsapprox_div p1 q0 {fmtq(mq)} hmq (by norm_num) (1 / 2 ^ 960) hησ (by norm_num)",M,e)
    return g,r,mq
def theorem(name,lo,hi,etk,slo):
    g,r,mq=gen(name,lo,hi,etk,slo)
    head=f'''theorem ratio_{name} (t : Float) (vt σ : ℝ) (ht : FSApprox t vt σ 1 ({fmtq(etk)} / 2 ^ 53))
    (hlo : {fmtq(lo)} ≤ vt) (hhi : vt ≤ {fmtq(hi)}) (hσ : σ ≤ {fmtq(hi)}) (hσ0 : 1 / 2 ^ {slo} ≤ σ) :
    FSApprox (Asin.asinRatio t) (vt * {exprP(0)} / (1 + vt * {exprQ(1)})) σ {fmtq(r[0])}
      ({fmtq(r[1]/u)} / 2 ^ 53) := by
  have hσp : 0 < σ := lt_of_lt_of_le (by positivity) hσ0
  have hσ1 : σ ≤ 1 := hσ.trans (by norm_num)
  have hk1 : σ ≤ {fmtq(hi)} * 1 := by rw [mul_one]; exact hσ
  have hη1 : (1 : ℝ) / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (1 * 1) := by norm_num
  have hησ : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * σ := by
    have : 1 / 2 ^ 960 * (1 / 2 ^ {slo}) ≤ 1 / 2 ^ 960 * σ :=
      mul_le_mul_of_nonneg_left hσ0 (by positivity)
    norm_num at this ⊢
    linarith
  have hησ' : 1 / 2 ^ 1075 ≤ 1 / 2 ^ 960 * (σ * 1) := by rw [mul_one]; exact hησ
  have one1 := one_sapprox'''
    body="\n".join(g.L).replace('fsapprox_mul ht a0 (1 / 2 ^ 960) hησ','fsapprox_mul ht a0 (1 / 2 ^ 960) hησ\'')
    return head+"\n"+body+"\n  exact r0\n", r, mq
if __name__=="__main__":
    txt,r,mq=theorem("A",F(0),F(1,4),F(0),60)
    print(txt[:3000]); print("r",float(r[0]),float(r[1]/u),"mq",float(mq))
