# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///
exec(open("model4.py").read().split("for xlo,xhi in")[0])
def mulA(a,b):
    B=(a[0]+a[1])*(b[0]+b[1]); return (a[0]*b[0], a[1]*b[0]+a[0]*b[1]+a[1]*b[1]+B*u+F(1,2**1075))
def divA(a,b,mb):
    Ma,ea=a; eb=b[1]; B=(Ma+ea)/(mb-eb)
    return (Ma/mb,(ea+Ma*eb/mb)/(mb-eb)+B*u+F(1,2**1075))
for xlo,xhi in [(F(1,2),F(55,100)),(F(55,100),F(6,10)),(F(6,10),F(7,10)),(F(7,10),F(8,10)),(F(8,10),F(9,10)),(F(9,10),F(975,1000)),(F(1,2),F(6,10)),(F(6,10),F(9,10))]:
    print(float(xlo),float(xhi),"E/2^-54=%.3f y>=%.4f  r err=%.3f"%a2b(xlo,xhi))
