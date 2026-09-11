// Independent host IEEE arithmetic for regression and scientific diagnostics.
// This module executes no WASM and is not formal proof evidence.
export class NumericalRejection extends Error {}
const finite=x=>{if(!Number.isFinite(x))throw new NumericalRejection('nonfinite intermediate');return x;};
const positive=x=>{finite(x);if(!(x>0))throw new NumericalRejection('nonpositive intermediate');return x;};
const guardBuffer=new DataView(new ArrayBuffer(8));
const exponent=x=>{guardBuffer.setFloat64(0,x);return (guardBuffer.getUint32(0)>>>20)&2047;};
function normalized(x,top){
  if(x===0)return 0;
  guardBuffer.setFloat64(0,Math.abs(x));
  const high=guardBuffer.getUint32(0),e=(high>>>20)&2047;
  if(e===0||top>=e+1021)throw new NumericalRejection('normalization range');
  guardBuffer.setUint32(0,((e+1021-top)<<20)|(high&0xfffff));
  return guardBuffer.getFloat64(0);
}
export function stateGuard(rho,m,t,E){
  positive(rho);finite(m);finite(t);positive(E);
  if(Math.abs(m)<=rho&&Math.abs(t)<=rho&&rho<E)return;
  const top=Math.max(exponent(rho),exponent(m),exponent(t),exponent(E));
  const r=normalized(rho,top),x=normalized(m,top),y=normalized(t,top),e=normalized(E,top);
  const residual=r*e-.5*(x*x+y*y);
  if(!(residual>2**-49))throw new NumericalRejection('internal energy margin');
}
export function side([rho,m,t,E]) {
  stateGuard(rho,m,t,E);
  const u=finite(m/rho),mu=finite(m*u),v=finite(t/rho),tv=finite(t*v);
  const sum=finite(mu+tv),half=finite(.5*sum),internal=positive(E-half);
  const p=positive(.4*internal),pr=positive(p/rho),rad=positive(1.4*pr);
  const sound=positive(Math.sqrt(rad)),speed=positive(Math.abs(u)+sound);
  const fm=finite(mu+p),ft=finite(t*u),enthalpy=finite(E+p),fe=finite(u*enthalpy);
  return {u,p,speed,flux:[m,fm,ft,fe]};
}
export function flux(left,right) {
  const l=side(left),r=side(right),alpha=positive(Math.max(l.speed,r.speed));
  return {alpha,value:l.flux.map((f,k)=>{
    const sum=finite(f+r.flux[k]),mean=finite(.5*sum),jump=finite(right[k]-left[k]);
    const viscosity=finite(alpha*jump),half=finite(.5*viscosity);
    return finite(mean-half);
  })};
}
export function cell(ratio,left,center,right) {
  positive(ratio);
  const l=flux(left,center),r=flux(center,right),alpha=Math.max(l.alpha,r.alpha);
  const courant=positive(ratio*alpha);if(courant>.5)throw new NumericalRejection('CFL ceiling');
  const state=center.map((q,k)=>{
    const difference=finite(r.value[k]-l.value[k]),increment=finite(ratio*difference);
    return finite(q-increment);
  });
  const next=side(state);
  return {state,p:next.p,alpha,courant};
}
export const swap=([rho,mx,my,E])=>[rho,my,mx,E];
export const scenarios=['four-quadrants','circular-blast','riemann'];
export const endTime=scenario=>scenario==='riemann'?.8:scenario==='circular-blast'?.15:.2;
export const riemannPrimitives=[
  [.029,.138,1.206,1.206], [.3,.5323,0,1.206],
  [.3,.5323,1.206,0], [1.5,1.5,0,0],
];
export const conservative=([p,rho,u,v])=>[rho,rho*u,rho*v,p/.4+.5*rho*(u*u+v*v)];
const riemannStates=riemannPrimitives.map(conservative);
export function initial(n,scenario='four-quadrants') {
  if(!Number.isInteger(n)||n<2||n%2)throw Error('mesh must be positive even');
  if(!scenarios.includes(scenario))throw Error('unknown scenario');
  return Array.from({length:n*n},(_,index)=>{
    const x=index%n,y=Math.floor(index/n);
    if(scenario==='riemann'){
      const fx=Math.max(0,Math.min(1,(4*n-5*x)/5)),fy=Math.max(0,Math.min(1,(4*n-5*y)/5));
      const weights=[fx*fy,(1-fx)*fy,fx*(1-fy),(1-fx)*(1-fy)];
      return Array.from({length:4},(_,k)=>((weights[0]*riemannStates[0][k]+weights[1]*riemannStates[1][k])+weights[2]*riemannStates[2][k])+weights[3]*riemannStates[3][k]);
    }
    if(scenario==='circular-blast'){const a=2*x+1-n,b=2*y+1-n;return [1,0,0,16*(a*a+b*b)<n*n?5:2.5];}
    const rho=x<n/2?(y<n/2?.25:.4):(y<n/2?.7:1);
    return [rho,0,0,2.5*rho];
  });
}
