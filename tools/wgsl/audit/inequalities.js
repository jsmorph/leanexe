// Exact rational checks for the analytic counterexample in the accompanying report.
// The analytic facts used (monotonicity, sinh(t)>=t, and exponential series
// bounds) are stated in the report. This is not a Lean proof.
const assert = require('node:assert/strict');
function gcd(a,b) { a=a<0n?-a:a; while(b) [a,b]=[b,a%b]; return a; }
class Q {
  constructor(n,d=1n) { n=BigInt(n); d=BigInt(d); if(d<0n) {n=-n;d=-d;} const g=gcd(n,d); this.n=n/g;this.d=d/g; }
  static of(x) { if(x instanceof Q)return x; const s=String(x); if(s.includes('.')) {const a=s.split('.');return new Q(a.join(''),10n**BigInt(a[1].length));} return new Q(s); }
  add(y){y=Q.of(y);return new Q(this.n*y.d+y.n*this.d,this.d*y.d);}
  sub(y){y=Q.of(y);return new Q(this.n*y.d-y.n*this.d,this.d*y.d);}
  mul(y){y=Q.of(y);return new Q(this.n*y.n,this.d*y.d);}
  div(y){y=Q.of(y);return new Q(this.n*y.d,this.d*y.n);}
  sq(){return this.mul(this);}
  lt(y){y=Q.of(y);return this.n*y.d<y.n*this.d;}
  toString(){return `${this.n}/${this.d}`;}
}
const q=Q.of, checks=[];
function less(name,a,b){assert(q(a).lt(b),name);checks.push(name);}
const delta=new Q(1n,2n**55n), eps=q('0.00001');
less('sqrt(delta^2+epsilon) < 0.003163',delta.sq().add(eps),q('0.003163').sq());
less('sqrt(delta^2+epsilon) > 0.003162',q('0.003162').sq(),eps);
less('a > 3.5e-14',q('0.000000000000035'),delta.mul(4).div('0.003163'));
less('q < 6e-13',delta.mul(64).div('0.003162'),'0.0000000000006');
less('v > 63.99',q('63.99').sq().mul(q(1).add(eps)),q(64).sq());
less('sqrt(2) > 1.414',q('1.414').sq(),2);
less('sqrt(2) < 1.415',2,q('1.415').sq());
less('t > 5.06e-11',q('0.0000000000506'),q('1.414').mul('0.00000000000056').mul('63.99'));
less('t < 6e-11',q('1.415').mul('0.0000000000006').mul(64),'0.00000000006');
less('u < 1e-24',q('1.415').mul(q('0.0000000000006').sq()),'0.000000000000000000000001');
// For 0<=x<1: cosh(x)<=1/(1-x^2), exp(x)<=1/(1-x).
const tUpper=q('0.00000000006'), uUpper=q('0.000000000000000000000001');
const denominatorUpper=q(2).div(q(1).sub(tUpper.sq())).add(1).add(q(1).div(q(1).sub(uUpper)));
less('softmax denominator < 4.001',denominatorUpper,'4.001');
less('attended amplitude > 1.61e-9',q('0.00000000161'),q(2).mul('63.99').mul('0.0000000000506').div('4.001'));
less('r1 > 2.57e-8',q('0.0000000257'),q(16).mul('0.00000000161'));
// f(r)=4r/sqrt(r^2+epsilon) is increasing. Evaluate at r=2.57e-8.
const r1Lower=q('0.0000000257');
less('sqrt(r1Lower^2+epsilon) < 0.003163',r1Lower.sq().add(eps),q('0.003163').sq());
less('n2 > 3.25e-5',q('0.0000325'),r1Lower.mul(4).div('0.003163'));
assert(q(16).mul('0.0000325').toString()===q('0.00052').toString());
// x>0.00052 implies GELU(x)>0.00026; therefore r2>32*0.00026.
less('r2 > 0.008',q('0.008'),q(32).mul('0.00026'));
// logit(r)=64r/sqrt(r^2+epsilon) is increasing.
const r2Lower=q('0.008');
less('ideal real logit > 59',q(59).sq().mul(r2Lower.sq().add(eps)),q(64).mul(r2Lower).sq());

// Reversing the sign of delta reverses r1 and x. GELU is not odd; bound
// its negative branch explicitly instead of assuming sign symmetry.
const aUpper=q(2).mul(64).mul(tUpper.div(q(1).sub(tUpper.sq())))
  .add(q('0.0000000000006').div(q(1).sub(uUpper))).div(4);
less('attended amplitude < 2e-9',aUpper,'0.000000002');
less('positive r1 < 3.3e-8',delta.add(q(16).mul('0.000000002')),'0.000000033');
less('positive expanded x < 0.001',q(64).mul('0.000000033').div('0.003162'),'0.001');
less('positive GELU tanh argument < 0.001',q('0.8').mul(q('0.001').add(q('0.05').mul(q('0.001').sq()).mul('0.001'))),'0.001');
// 0<=tanh(y)<=y gives |GELU(-x)| > 0.49*x here.
less('negative GELU magnitude factor > 0.49',q('0.49'),q(1).sub('0.001').div(2));
less('negative-case residual2 magnitude > 0.008',q('0.008'),q(32).mul('0.49').mul('0.00052'));

// Exact checks of rounded-up bounds, including subnormal contributions.
const ur=new Q(1n,2n**24n), vr=new Q(1n,2n**53n);
const eta=new Q(1n,2n**150n), xi=new Q(1n,2n**1075n);
const rr=new Q(1018n,2n**52n), hr=q(32).add(rr.mul(4)), sr=hr.mul(4);
const d32r=ur.mul(6).add(ur.sq()).mul(sr)
  .add(eta.mul(q(1).add(ur)).mul(hr.add(16)))
  .add(eta.sq().mul(4)).add(eta.mul(7)).div(q(1).sub(ur.mul(4)));
const e32r=d32r.add(vr.mul(sr.add(d32r).add(4))).add(xi);
const d64r=vr.mul(4).mul(sr).add(xi.mul(7)).div(q(1).sub(vr.mul(4)));
const e64r=d64r.add(vr.mul(sr.add(d64r).add(4))).add(xi);
less('binary32 head error < 0.000046',e32r,'0.000046');
less('head replacement error < 0.000046',e32r.add(e64r),'0.000046');
less('whole mixed implementation cap < 128.000046',q(128).add(rr.mul(16)).add(e32r),'128.000046');
less('whole binary64 implementation cap < 128.000000000004',q(128).add(rr.mul(16)).add(e64r),'128.000000000004');
console.log(JSON.stringify({exactRationalChecks:checks.length,checks,conclusion:'ideal real logit > 59; rounded-up error caps verified'},null,2));

const B=4,u32=2**-24,u64=2**-53,eta32=2**-150;
const r=(254*B+2)*2**-52;
const H1=8*B+4*r, S=B*H1;
const c32=(6*u32+u32*u32)/(1-4*u32);
const underflow=(eta32*(1+u32)*(H1+4*B)+4*eta32**2+7*eta32)/(1-4*u32);
const D32=c32*S+underflow;
const E32=D32+u64*(S+D32+B); // +2^-1075, too small for Number.
const D64=4*u64/(1-4*u64)*S; // +7*2^-1075/(1-4*u64).
const E64=D64+u64*(S+D64+B); // +2^-1075.
console.log(JSON.stringify({B,realLogitMagnitude:8*B*B+B,realLogitDiameter:8*B*B,
  localNormError:r,headAbsoluteProductSum:S,head32Error:E32,head64Error:E64,
  full32ErrorCap:8*B*B+4*B*r+E32,full64ErrorCap:8*B*B+4*B*r+E64},null,2));
