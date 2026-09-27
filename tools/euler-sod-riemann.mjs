import assert from 'node:assert/strict';
// Independent scientific oracle, not a Lean theorem or a runtime dependency.
// Relations: https://www.clawpack.org/riemann_book/html/Euler.html
// Standard zero-velocity Sod data; gamma=7/5. No general vacuum solver claim.
const gamma=1.4,gm=.4,gp=2.4,a=Math.sqrt(gamma),ar=Math.sqrt(gamma*.1/.125);
const left=[1,0,2.5],right=[.125,0,.25];
const curve=(p,rho,p0,c)=>p>p0?(p-p0)*Math.sqrt(2/(gp*rho)/(p+gm/gp*p0)):
  2*c/gm*(Math.pow(p/p0,gm/(2*gamma))-1);
const residual=p=>curve(p,1,1,a)+curve(p,.125,.1,ar);
let lo=.1,hi=1;
assert.ok(residual(lo)<0&&residual(hi)>0);
for(let i=0;i<100;i++){const mid=(lo+hi)/2;if(residual(mid)>0)hi=mid;else lo=mid;}
const p=(lo+hi)/2,u=(curve(p,.125,.1,ar)-curve(p,1,1,a))/2;
const rhol=Math.pow(p,1/gamma),rhor=.125*(p/.1+gm/gp)/(gm/gp*p/.1+1);
const head=-a,tail=u-Math.sqrt(gamma*p/rhol),contact=u;
const shock=ar*Math.sqrt(gp/(2*gamma)*p/.1+gm/(2*gamma));
const state=(rho,v,pressure)=>[rho,rho*v,pressure/gm+.5*rho*v*v];
const starL=state(rhol,u,p),starR=state(rhor,u,p);
const flux=([rho,m,E])=>{const v=m/rho,pr=gm*(E-.5*m*v);return[m,m*v+pr,v*(E+pr)];};
const fr=flux(right),fs=flux(starR);
const jumpResidual=right.map((x,k)=>fr[k]-fs[k]-shock*(x-starR[k]));
assert.ok(Math.abs(residual(p))<1e-13);
assert.ok(jumpResidual.every(x=>Math.abs(x)<1e-13));
assert.ok(head<tail&&tail<contact&&contact<shock);
function fanIntegral(l,r){
  const c0=(5*a-l)/6,c1=(5*a-r)/6;
  // Integrate each polynomial power without subtracting nearly equal powers.
  const power=k=>{let sum=0;for(let j=0;j<=k;j++)sum+=c0**(k-j)*c1**j;return(r-l)*sum/(k+1);};
  const i5=power(5),i6=power(6),i7=power(7);
  return[i5/a**5,5*(a*i5-i6)/a**5,2.5*i7/a**7+12.5*(a*a*i5-2*a*i6+i7)/a**5];
}
function integral(l,r){
  const boundaries=[l,...[head,tail,contact,shock].filter(x=>l<x&&x<r),r];
  const sum=[0,0,0];
  for(let i=0;i+1<boundaries.length;i++){
    const x=boundaries[i],y=boundaries[i+1],mid=(x+y)/2;
    const segment=mid<head?left:mid<tail?null:mid<contact?starL:mid<shock?starR:right;
    const part=segment?segment.map(v=>v*(y-x)):fanIntegral(x,y);
    for(let k=0;k<3;k++)sum[k]+=part[k];
  }
  return sum;
}
export function average(xl,xr,t=.2){return integral((xl-.5)/t,(xr-.5)/t).map(x=>x*t/(xr-xl));}
const total=integral(-2.5,2.5).map(x=>.2*x);
for(const [actual,expected] of total.map((x,k)=>[x,[.5625,.18,1.375][k]]))assert.ok(Math.abs(actual-expected)<1e-13);
export const referenceSummary={pStar:p,uStar:u,waveSpeeds:[head,tail,contact,shock],pressureResidual:residual(p),shockJumpResidual:jumpResidual,exactSolutionIntegrals:total};
