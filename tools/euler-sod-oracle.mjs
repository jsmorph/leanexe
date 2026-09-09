import assert from 'node:assert/strict';
import {pathToFileURL} from 'node:url';
// Host design/regression oracle only: no generated-Wasm or formal-proof claim.
const finite = x => {assert.ok(Number.isFinite(x), `nonfinite ${x}`); return x;};
const positive = x => {finite(x); assert.ok(x > 0, `nonpositive ${x}`); return x;};
export function side([rho,m,E]) {
  positive(rho); finite(m); finite(E);
  assert.ok(Math.abs(m) <= rho && E >= rho, 'conservative domain');
  const u=finite(m/rho), mu=finite(m*u), half=finite(.5*mu);
  const internal=positive(E-half), p=positive(.4*internal);
  const pr=positive(p/rho), rad=positive(1.4*pr), c=positive(Math.sqrt(rad));
  const speed=positive(Math.abs(u)+c), fm=finite(mu+p), ep=finite(E+p), fe=finite(u*ep);
  return {u,p,speed,flux:[m,fm,fe]};
}
export function flux(left,right) {
  const l=side(left),r=side(right),alpha=positive(Math.max(l.speed,r.speed));
  return {alpha, value:l.flux.map((x,i)=>{
    const sum=finite(x+r.flux[i]),mean=finite(.5*sum),jump=finite(right[i]-left[i]);
    const visc=finite(alpha*jump),half=finite(.5*visc);
    return finite(mean-half);
  })};
}
export function run(n=100) {
  const dx=1/n, cfl=.45, final=.2;
  let cells=Array.from({length:n},(_,i)=>i<n/2?[1,0,2.5]:[.125,0,.25]);
  let t=0,steps=0,maxMachGuard=0,minEnergyRatio=Infinity,maxCfl=0;
  const balance=[0,0,0], initial=[0,0,0];
  for(const q of cells)for(let k=0;k<3;k++)initial[k]+=q[k]*dx;
  while(t<final) {
    assert.ok(++steps<10000,'step budget');
    const faces=Array.from({length:n+1},(_,i)=>flux(cells[Math.max(0,i-1)],cells[Math.min(n-1,i)]));
    const alpha=positive(Math.max(...faces.map(f=>f.alpha)));
    const candidate=positive(finite(cfl*dx)/alpha),remaining=positive(final-t);
    const dt=positive(Math.min(candidate,remaining)),ratio=positive(dt/dx);
    const courant=positive(ratio*alpha);
    assert.ok(courant<=.5,'CFL acceptance ceiling');
    maxCfl=Math.max(maxCfl,courant);
    const next=cells.map((q,i)=>q.map((v,k)=>finite(v-finite(ratio*finite(faces[i+1].value[k]-faces[i].value[k])))));
    for(const q of next){side(q);maxMachGuard=Math.max(maxMachGuard,Math.abs(q[1])/q[0]);minEnergyRatio=Math.min(minEnergyRatio,q[2]/q[0]);}
    for(let k=0;k<3;k++)balance[k]+=dt*(faces[n].value[k]-faces[0].value[k]);
    const nextTime=positive(t+dt);assert.ok(nextTime>t && nextTime<=final,'time progress');
    cells=next;t=nextTime;
  }
  const total=[0,0,0];for(const q of cells)for(let k=0;k<3;k++)total[k]+=q[k]*dx;
  return {cells,n,steps,t,maxMachGuard,minEnergyRatio,maxCfl,minRho:Math.min(...cells.map(q=>q[0])),minP:Math.min(...cells.map(q=>side(q).p)),balanceResidual:total.map((x,k)=>x-initial[k]+balance[k])};
}
if(process.argv[1] && import.meta.url===pathToFileURL(process.argv[1]).href){const {cells,...summary}=run();console.log(JSON.stringify(summary,null,2));}
