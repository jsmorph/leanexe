exec(open("alib.py").read())
def ihorner(coeffs,lo,hi):
    L=U=coeffs[-1]; parts={len(coeffs)-1:(L,U)}
    for i in range(len(coeffs)-2,-1,-1):
        cands=[lo*L,lo*U,hi*L,hi*U]
        L,U=coeffs[i]+min(cands),coeffs[i]+max(cands)
        parts[i]=(L,U)
    return parts
def pmaxr(coeffs,lo,hi,N=0):
    L,U=ihorner(coeffs,lo,hi)[0]; return max(abs(L),abs(U))
def pminr(coeffs,lo,hi,N=0):
    L,U=ihorner(coeffs,lo,hi)[0]; return min(abs(L),abs(U)) if L*U>0 else F(0)
for xlo,xhi in [(F(1,2),F(6,10)),(F(6,10),F(9,10)),(F(9,10),F(975,1000)),(F(1,2),F(55,100)),(F(55,100),F(6,10))]:
    print(float(xlo),float(xhi),"E/2^-54=%.3f y>=%.4f  r err=%.3f"%a2b(xlo,xhi))
