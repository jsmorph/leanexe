// Independent host IEEE arithmetic for regression and scientific diagnostics.
// This module executes no WASM and is not formal proof evidence.
const finite=x=>{if(!Number.isFinite(x))throw Error('nonfinite intermediate');return x;};
const positive=x=>{finite(x);if(!(x>0))throw Error('nonpositive intermediate');return x;};
export function side([rho,m,t,E]) {
  positive(rho);finite(m);finite(t);positive(E);
  if(!(Math.abs(m)<=rho && Math.abs(t)<=rho && rho<E))throw Error('state outside sufficient domain');
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
  const courant=positive(ratio*alpha);if(courant>.5)throw Error('CFL ceiling');
  const state=center.map((q,k)=>{
    const difference=finite(r.value[k]-l.value[k]),increment=finite(ratio*difference);
    return finite(q-increment);
  });
  const next=side(state);
  return {state,p:next.p,alpha,courant};
}
export const swap=([rho,mx,my,E])=>[rho,my,mx,E];
export function initial(n) {
  if(!Number.isInteger(n)||n<2||n%2)throw Error('mesh must be positive even');
  return Array.from({length:n*n},(_,index)=>{
    const x=index%n,y=Math.floor(index/n);
    const rho=x<n/2?(y<n/2?.25:.4):(y<n/2?.7:1);
    return [rho,0,0,2.5*rho];
  });
}
