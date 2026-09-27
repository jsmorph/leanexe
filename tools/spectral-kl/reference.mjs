// Independent test/reference computation: direct solves inside quadrature.
// This deliberately does not use a generalized eigendecomposition.
export function solve(matrix,rhs,m) {
  const a=Array.from(matrix), b=Array.from(rhs);
  for(let k=0;k<m;k++) {
    let pivot=k;
    for(let i=k+1;i<m;i++) if(Math.abs(a[i*m+k])>Math.abs(a[pivot*m+k])) pivot=i;
    if(!Number.isFinite(a[pivot*m+k]) || Math.abs(a[pivot*m+k])<1e-30) throw new Error('Singular reference solve');
    for(let j=k;j<m;j++) [a[k*m+j],a[pivot*m+j]]=[a[pivot*m+j],a[k*m+j]];
    [b[k],b[pivot]]=[b[pivot],b[k]];
    for(let i=k+1;i<m;i++) {
      const scale=a[i*m+k]/a[k*m+k];
      for(let j=k+1;j<m;j++) a[i*m+j]-=scale*a[k*m+j];
      b[i]-=scale*b[k];
    }
  }
  const out=new Float64Array(m);
  for(let i=m-1;i>=0;i--) {
    let s=b[i];
    for(let j=i+1;j<m;j++) s-=a[i*m+j]*out[j];
    out[i]=s/a[i*m+i];
  }
  return out;
}
export function referenceScore(p,q,m,eta,steps=512) {
  const delta=Float64Array.from({length:m},(_,i)=>p[i]-q[i]);
  function f(r) {
    const a=Float64Array.from({length:m*m},(_,i)=>r*p[m+i]+(1-r)*q[m+i]+(Math.floor(i/m)===i%m?eta:0));
    const x=solve(a,delta,m);
    return (1-r)*delta.reduce((s,d,i)=>s+d*x[i],0);
  }
  let total=f(0);
  for(let i=1;i<steps;i++) total+=(i%2?4:2)*f(i/steps);
  return total/(3*steps);
}
export function referenceMoments(rows,m) {
  const n=rows.length/m, result=new Float64Array(m+m*m);
  // Observation-first traversal, independent from the executable's entry-first traversal.
  for(let r=0;r<n;r++) {
    for(let j=0;j<m;j++) {
      result[j]+=rows[r*m+j];
      for(let k=0;k<m;k++) result[m+j*m+k]+=rows[r*m+j]*rows[r*m+k];
    }
  }
  return result.map(x=>x/n);
}
export function observations(n,m,seed,shift=0) {
  let state=seed>>>0;
  const rand=()=>{state^=state<<13;state^=state>>>17;state^=state<<5;return (state>>>0)/2**32-0.5;};
  const a=new Float32Array(n*m);
  for(let i=0;i<n;i++) {
    const latent=rand();
    for(let j=0;j<m;j++) a[i*m+j]=0.4*rand()+0.3*latent*(1+j%3)+shift*(j===0?1:0.2);
  }
  return a;
}
