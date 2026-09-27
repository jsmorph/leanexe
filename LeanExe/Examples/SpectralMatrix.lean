import LeanExe.Examples.SpectralKL

namespace LeanExe.Examples.SpectralMatrix
open LeanExe.IEEE64
open LeanExe.Examples.SpectralKL (Result kernel40Polynomial)

def magnitude (x : UInt64) : UInt64 := x &&& 0x7FFFFFFFFFFFFFFF
def negate (x : UInt64) : UInt64 := x ^^^ 0x8000000000000000

/-- Row-major feature observations → means followed by full uncentered Gram
matrix. Empty output rejects invalid shape or samples. Up to 32 features,
524288 input words, finite values in [-16,16]. -/
def moments (rows : Array UInt64) (width : UInt64) : Array UInt64 := Id.run do
  if width == 0 || width > 32 || rows.isEmpty || rows.size > 524288 then
    return #[]
  let m := width.toNat
  if rows.size % m != 0 then return #[]
  let n := rows.size / m
  let mut r := 0
  let mut count : UInt64 := 0
  while r < n do
    count := addBits count 0x3FF0000000000000
    r := r + 1
  let mut i := 0
  while i < rows.size do
    if magnitude rows[i]! > 0x4030000000000000 then return #[]
    i := i + 1
  let mut out := Array.replicate (m+m*m) (0 : UInt64)
  let mut j := 0
  while j < m do
    let mut sum : UInt64 := 0
    r := 0
    while r < n do
      sum := addBits sum rows[r*m+j]!
      r := r + 1
    out := out.set! j (divBits sum count)
    let mut k := j
    while k < m do
      sum := 0
      r := 0
      while r < n do
        sum := addBits sum (mulBits rows[r*m+j]! rows[r*m+k]!)
        r := r + 1
      let second := divBits sum count
      out := out.set! (m+j*m+k) second
      out := out.set! (m+k*m+j) second
      k := k + 1
    j := j + 1
  return out

/-- Add the ridge term to an uncentered second-moment matrix. -/
def regularized (moments : Array UInt64) (m : Nat) (eta : UInt64) : Array UInt64 := Id.run do
  let mut out := Array.replicate (m*m) (0 : UInt64)
  let mut i := 0
  while i < m do
    let mut j := 0
    while j < m do
      out := out.set! (i*m+j) (if i == j then addBits moments[m+i*m+j]! eta else moments[m+i*m+j]!)
      j := j+1
    i := i+1
  return out

def meanDifference (p q : Array UInt64) (m : Nat) : Array UInt64 := Id.run do
  let mut out := Array.replicate m (0 : UInt64)
  let mut i := 0
  while i < m do
    out := out.set! i (subBits p[i]! q[i]!)
    i := i+1
  return out

/-- Lower Cholesky factor, or empty on a nonpositive/nonfinite pivot. -/
def cholesky (b : Array UInt64) (m : Nat) : Array UInt64 := Id.run do
  let mut l := Array.replicate (m*m) (0 : UInt64)
  let mut i := 0
  while i < m do
    let mut j := 0
    while j ≤ i do
      let mut s := b[i*m+j]!
      let mut k := 0
      while k < j do
        s := subBits s (mulBits l[i*m+k]! l[j*m+k]!)
        k := k+1
      if i == j then
        if s == 0 || s ≥ 0x7FF0000000000000 then return #[]
        l := l.set! (i*m+j) (sqrtBits s)
      else
        l := l.set! (i*m+j) (divBits s l[j*m+j]!)
      j := j+1
    i := i+1
  return l

/-- Solve L T = A by columns. -/
def forwardMatrix (l a : Array UInt64) (m : Nat) : Array UInt64 := Id.run do
  let mut t := Array.replicate (m*m) (0 : UInt64)
  let mut i := 0
  while i < m do
    let mut j := 0
    while j < m do
      let mut s := a[i*m+j]!
      let mut k := 0
      while k < i do
        s := subBits s (mulBits l[i*m+k]! t[k*m+j]!)
        k := k+1
      t := t.set! (i*m+j) (divBits s l[i*m+i]!)
      j := j+1
    i := i+1
  return t

def forwardVector (l d : Array UInt64) (m : Nat) : Array UInt64 := Id.run do
  let mut z := Array.replicate m (0 : UInt64)
  let mut i := 0
  while i < m do
    let mut s := d[i]!
    let mut k := 0
    while k < i do
      s := subBits s (mulBits l[i*m+k]! z[k]!)
      k := k+1
    z := z.set! i (divBits s l[i*m+i]!)
    i := i+1
  return z

/-- Solve C Lᵀ = T by rows and restore symmetry after rounding. -/
def whiten (l t : Array UInt64) (m : Nat) : Array UInt64 := Id.run do
  let mut c := Array.replicate (m*m) (0 : UInt64)
  let mut i := 0
  while i < m do
    let mut j := 0
    while j < m do
      let mut s := t[i*m+j]!
      let mut k := 0
      while k < j do
        s := subBits s (mulBits l[j*m+k]! c[i*m+k]!)
        k := k+1
      c := c.set! (i*m+j) (divBits s l[j*m+j]!)
      j := j+1
    i := i+1
  i := 0
  while i < m do
    let mut j := i+1
    while j < m do
      let s := mulBits 0x3FE0000000000000 (addBits c[i*m+j]! c[j*m+i]!)
      c := c.set! (i*m+j) s
      c := c.set! (j*m+i) s
      j := j+1
    i := i+1
  return c

/-- Jacobi state stores the matrix followed by coordinates of the mean difference.
A rotation updates both, avoiding construction of an eigenvector matrix. -/
def rotate (state : Array UInt64) (m p q : Nat) : Array UInt64 := Id.run do
  let mut c := state
  let off := c[p*m+q]!
  let tau := divBits (subBits c[q*m+q]! c[p*m+p]!) (mulBits 0x4000000000000000 off)
  let denominator := addBits (magnitude tau) (sqrtBits (addBits 0x3FF0000000000000 (mulBits tau tau)))
  let tm := divBits 0x3FF0000000000000 denominator
  let rotation := if tau ≥ 0x8000000000000000 then negate tm else tm
  let cosine := divBits 0x3FF0000000000000 (sqrtBits (addBits 0x3FF0000000000000 (mulBits rotation rotation)))
  let sine := mulBits rotation cosine
  c := c.set! (p*m+p) (subBits c[p*m+p]! (mulBits rotation off))
  c := c.set! (q*m+q) (addBits c[q*m+q]! (mulBits rotation off))
  c := c.set! (p*m+q) 0
  c := c.set! (q*m+p) 0
  let mut k := 0
  while k < m do
    if k != p && k != q then
      let kp := c[k*m+p]!
      let kq := c[k*m+q]!
      let np := subBits (mulBits cosine kp) (mulBits sine kq)
      let nq := addBits (mulBits sine kp) (mulBits cosine kq)
      c := c.set! (k*m+p) np
      c := c.set! (p*m+k) np
      c := c.set! (k*m+q) nq
      c := c.set! (q*m+k) nq
    k := k+1
  let zp := c[m*m+p]!
  let zq := c[m*m+q]!
  c := c.set! (m*m+p) (subBits (mulBits cosine zp) (mulBits sine zq))
  c := c.set! (m*m+q) (addBits (mulBits sine zp) (mulBits cosine zq))
  return c

def jacobi (matrix coordinates : Array UInt64) (m : Nat) : Array UInt64 := Id.run do
  let mut state := matrix ++ coordinates
  let mut sweep := 0
  let mut converged := false
  while sweep < 32 && !converged do
    let mut largest : UInt64 := 0
    let mut p := 0
    while p < m do
      let mut q := p+1
      while q < m do
        let off := magnitude state[p*m+q]!
        if off > largest then largest := off
        if off > 0x3D50000000000000 then state := rotate state m p q
        q := q+1
      p := p+1
    converged := largest ≤ 0x3D50000000000000
    sweep := sweep+1
  if !converged then return #[]
  return state

def spectralSum (eigen : Array UInt64) (m : Nat) : Result := Id.run do
  let mut answer : UInt64 := 0
  let mut i := 0
  while i < m do
    let delta := subBits eigen[i*m+i]! 0x3FF0000000000000
    if magnitude delta > 0x3FE0000000000000 then return ⟨2, 0⟩
    let z := eigen[m*m+i]!
    answer := addBits answer (mulBits (mulBits z z) (kernel40Polynomial delta))
    i := i+1
  if magnitude answer ≥ 0x7FF0000000000000 then return ⟨3, 0⟩
  return ⟨0, answer⟩

def validMoments (p q : Array UInt64) (m : Nat) : Bool := Id.run do
  if p.size != m+m*m || q.size != m+m*m then return false
  let mut idx := 0
  while idx < p.size do
    if magnitude p[idx]! > 0x4070000000000000 || magnitude q[idx]! > 0x4070000000000000 then
      return false
    idx := idx+1
  let mut i := 0
  while i < m do
    let mut j := 0
    while j < m do
      if magnitude (subBits p[m+i*m+j]! p[m+j*m+i]!) != 0 ||
          magnitude (subBits q[m+i*m+j]! q[m+j*m+i]!) != 0 then return false
      j := j+1
    i := i+1
  return true

/-- Dense score proposal, status 1: input; 2: spectral domain;
3: factorization/finite result; 4: convergence. The public CLI sends this
proposal to the proved residual checker before returning a final score.
This function alone does not provide a matrix error guarantee. -/
def score (p q : Array UInt64) (width eta : UInt64) : Result :=
  if width == 0 || width > 32 || eta < 0x3EB0000000000000 || eta > 0x4070000000000000 then ⟨1, 0⟩
  else
    let m := width.toNat
    if !validMoments p q m then ⟨1, 0⟩
    else
      let l := cholesky (regularized q m eta) m
      if l.isEmpty then ⟨3, 0⟩
      else
        let c := whiten l (forwardMatrix l (regularized p m eta) m) m
        let z := forwardVector l (meanDifference p q m) m
        let eigen := jacobi c z m
        if eigen.isEmpty then ⟨4, 0⟩ else spectralSum eigen m

end LeanExe.Examples.SpectralMatrix
