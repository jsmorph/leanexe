exec(open('genmid.py').read().split('for alo,ahi,ch,n in')[0])
def Q(x): return fmtq(x)
U54=F(2)**-54
def plan2(alo,ahi,chain,n):
    lo=(1-ahi)/2; hi=(1-alo)/2
    shi=upq(F(math.sqrt(float(hi)))*(1+F(1,10**9)))
    slo=dnq(F(math.sqrt(float(lo)))*(1-F(1,10**9)))
    g,r,mq=gen(chain[0],chain[1],chain[2],F(0),56)
    Mr,er=r[0],r[1]
    es=shi*u
    VWLO=dnq((slo-es)*(1-F(1,2**20)),10**9)
    Mtw=upq((es+shi/F(2)**20)*(2*shi+es),10**15)
    esw=2*(shi+es)*u
    mb=dnq((slo-es)+VWLO,10**6)
    Bc=upq(Mtw/(mb-esw),10**15)
    ec=(0+Mtw*esw/mb)/(mb-esw)+Bc*u+F(1,2**1075)
    Mc=upq(Mtw/mb,10**15)
    Bc2=upq(2*(Mc+ec),10**15); ec2=2*ec+Bc2*u+F(1,2**1075)
    vlob=F(1,10**16)
    Blo=upq(vlob+2*Mc+ec2,10**15); elo=ec2+Blo*u
    MrA=Mr*hi; erA=er*hi
    Bsr=upq((2*shi+2*es)*(MrA+erA),10**9); esr=2*es*MrA+2*shi*erA+2*es*erA+Bsr*u+F(1,2**1075)
    Mp=2*shi*MrA+Blo
    gp,hp=hu(Mp+esr+elo); ep=esr+elo+hp
    vwhi=shi+es
    Mq=upq(max(abs(vh4-2*VWLO),abs(vh4-2*vwhi)),10**9)
    gq,hq=hu(Mq); eq=hq
    gpq,hpq=hu(Mp+Mq+ep+eq); epq=ep+eq+hpq
    mbp=dnq(slo+VWLO,10**6)
    small=upq(Mtw*es/(mbp*mb),10**30)
    E=epq+F(1,2**64)+2*shi**3*kap+2*small
    return locals()
def emit(name,alo,ahi,chain,n,Enum):
    d=plan2(alo,ahi,chain,n)
    globals().update(d)
    h=F(2)**(n-1)/F(2)**1074
    print(name,"E units",float(E/U54),"Enum",float(Enum/U54),"h",float(h/U54))
    assert E<=Enum<h
    yb = "1" if n==1023 else "1 / 2"
    return f'''
theorem mid_{name} (x : Float) (hx : Finite x.toBits) (h1 : {Q(alo)} ≤ |value x.toBits|)
    (h2 : |value x.toBits| ≤ {Q(ahi)}) (hy : {yb} + {Q(Enum)} ≤ Real.arcsin |value x.toBits|) :
    F64SignedRounding.WithinSteps 1 (Real.arcsin |value x.toBits|) (midTail (tOf x)).toBits := by
  obtain ⟨htf, htv⟩ := t_exact x hx (by linarith) (by linarith)
  set a := |value x.toBits| with ha
  set vt := (1 - a) / 2 with hvt
  have hvlo : {Q(lo)} ≤ vt := by rw [hvt]; linarith
  have hvhi : vt ≤ {Q(hi)} := by rw [hvt]; linarith
  have hvtp : 0 < vt := lt_of_lt_of_le (by norm_num) hvlo
  have ht : FSApprox (tOf x) vt vt 1 0 :=
    (fsapprox_input (tOf x) htf vt hvtp (by linarith) (by rw [htv, abs_of_pos hvtp])).congr htv
  have hr := ratio_{chain[0]} (tOf x) vt vt (ht.mono le_rfl (by norm_num)) (by linarith) hvhi hvhi
    (le_trans (by norm_num) hvlo)
  rw [ratio_eval] at hr
  obtain ⟨hrA, hrM⟩ := Log1pTheoremTail.fsapprox_abs hr hvhi
  set rv := vt * eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt with hrv
  have hrM' : |rv| ≤ {Q(MrA)} := hrM.trans (le_of_eq (by norm_num))
  have hrA' := Approx.mono hrA (e' := {Q(erA)}) (le_of_eq (by norm_num))
  -- `s = √t`
  have htA : FApprox (tOf x) vt 0 := ⟨htf, by rw [htv, sub_self, abs_zero]⟩
  have hsqrt0 : 0 < Real.sqrt vt := Real.sqrt_pos.mpr hvtp
  have hsqv : Real.sqrt vt * Real.sqrt vt = vt := Real.mul_self_sqrt hvtp.le
  have hsqhi : Real.sqrt vt ≤ {Q(shi)} := by
    rw [Real.sqrt_le_left (by norm_num)]
    nlinarith
  have hsqlo : {Q(slo)} ≤ Real.sqrt vt := by
    rw [Real.le_sqrt (by norm_num) hvtp.le]
    nlinarith
  have hs := Approx.mono (fapprox_sqrt htA vt vt hvtp le_rfl hvtp le_rfl (Real.sqrt vt)
    (by rw [add_zero])) (e' := {Q(shi)} / 2 ^ 53) (by
      rw [zero_div, zero_add]
      exact div_le_div_of_nonneg_right hsqhi (by positivity))
  set s := (tOf x).sqrt with hsd
  set vs := value s.toBits with hvs
  obtain ⟨hes1, hes2⟩ := abs_le.mp hs.2
  have hvs0 : 0 < vs := by
    have : ({Q(shi)} : ℝ) / 2 ^ 53 < {Q(slo)} := by norm_num
    linarith
  -- `w`, the high part of `s`
  have hse : 506 ≤ Wasm.IEEE64.exponent s.toBits :=
    Log1pTheoremCorr.exponent_ge _ 506 (-517) (by norm_num) (by norm_num) (by
      rw [abs_of_pos hvs0, show (2 : ℝ) ^ (-517 : ℤ) = 1 / 2 ^ 517 by norm_num]
      have : (1 : ℝ) / 2 ^ 517 ≤ {Q(slo)} - {Q(shi)} / 2 ^ 53 := by norm_num
      linarith)
  obtain ⟨hwf, hwle, hwd, q, hq, hqm⟩ := trunc_facts s.toBits hvs0 hs.1 hse
  have hwb : (wOf s).toBits = s.toBits &&& 0xFFFFFFFF00000000 := by
    unfold wOf
    rw [F64Bits.toBits_ofBits, not_nan_of_finite hwf]
    simp only [Bool.false_eq_true, ite_false]
  rw [← hwb] at hwf hwle hwd hqm
  set w := wOf s with hwdef
  set vw := value w.toBits with hvw
  have hvwlo : {Q(VWLO)} ≤ vw := by
    have : {Q(VWLO)} ≤ vs * (1 - 1 / 2 ^ 20) := by
      have h3 : ({Q(slo)} - {Q(shi)} / 2 ^ 53) * (1 - 1 / 2 ^ 20) ≤ vs * (1 - 1 / 2 ^ 20) :=
        mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
      have h4 : ({Q(VWLO)} : ℝ) ≤ ({Q(slo)} - {Q(shi)} / 2 ^ 53) * (1 - 1 / 2 ^ 20) := by norm_num
      linarith
    linarith
  have hvw0 : 0 < vw := lt_of_lt_of_le (by norm_num) hvwlo
  have hvwhi : vw ≤ {Q(shi)} + {Q(shi)} / 2 ^ 53 := by linarith
  -- `w * w` and `t - w * w` are exact
  have hww := F64ExactProduct.mul_exact_scaled w.toBits w.toBits hwf hwf q q
    (Wasm.IEEE64.exponent s.toBits - 1 + 32) (Wasm.IEEE64.exponent s.toBits - 1 + 32) hqm hqm
    (by nlinarith) (by omega) (by
      have := AsinTheoremSupport.exponent_lt_one s.toBits (by
        rw [abs_of_pos hvs0]
        have : ({Q(shi)} : ℝ) + {Q(shi)} / 2 ^ 53 < 1 := by norm_num
        linarith)
      omega)
  rw [← F64Bits.toBits_mul] at hww
  have hwwv : value (w * w).toBits = vw * vw := hww.2.1
  -- `|t - w²|` is small
  have hdw : |Real.sqrt vt - vw| ≤ {Q(shi)} / 2 ^ 53 + {Q(shi)} / 2 ^ 20 := by
    rw [abs_le]
    constructor
    · linarith
    · have : vs / 2 ^ 20 ≤ ({Q(shi)} + {Q(shi)} / 2 ^ 53) / 2 ^ 20 :=
        div_le_div_of_nonneg_right (by linarith) (by norm_num)
      have h5 : ({Q(shi)} + {Q(shi)} / 2 ^ 53 : ℝ) / 2 ^ 20 ≤ {Q(shi)} / 2 ^ 20 + {Q(shi)} / 2 ^ 53 := by
        norm_num
      linarith
  have htw0 : |vt - vw * vw| ≤ {Q(Mtw)} := by
    rw [show vt - vw * vw = (Real.sqrt vt - vw) * (Real.sqrt vt + vw) by rw [← hsqv]; ring,
      abs_mul, abs_of_pos (by linarith : 0 < Real.sqrt vt + vw)]
    have h3 : Real.sqrt vt + vw ≤ 2 * {Q(shi)} + {Q(shi)} / 2 ^ 53 := by linarith
    have h4 := mul_le_mul hdw h3 (by positivity) (by positivity)
    have h5 : ({Q(shi)} / 2 ^ 53 + {Q(shi)} / 2 ^ 20 : ℝ) * (2 * {Q(shi)} + {Q(shi)} / 2 ^ 53) ≤
        {Q(Mtw)} := by norm_num
    linarith
  have hwwt1 : vw * vw ≤ 2 * vt := by
    have := (abs_le.mp htw0).1
    have : ({Q(Mtw)} : ℝ) ≤ {Q(lo)} := by norm_num
    linarith
  have hwwt2 : vt ≤ 2 * (vw * vw) := by
    have := (abs_le.mp htw0).2
    have : ({Q(Mtw)} : ℝ) ≤ {Q(lo)} := by norm_num
    linarith
  have htw := F64Exact.sub_exact (tOf x).toBits (w * w).toBits htf hww.1 (by rw [htv]; exact hvtp)
    (by rw [hwwv]; positivity) (by rw [hwwv, htv]; exact hwwt1) (by rw [hwwv, htv]; exact hwwt2)
    (by rw [htv]; linarith [(by norm_num : ({Q(hi)} : ℝ) < 2 ^ 900)])
    (by rw [hwwv]; nlinarith [(by norm_num : (4 : ℝ) < 2 ^ 900)])
  rw [← F64Bits.toBits_sub, htv, hwwv] at htw
  have htwA : FApprox (tOf x - w * w) (vt - vw * vw) 0 := ⟨htw.1, by rw [htw.2, sub_self, abs_zero]⟩
  -- `s + w` and `c`
  have hsw := fapprox_add (approx_self s.toBits hs.1) (approx_self w.toBits hwf)
    (2 * ({Q(shi)} + {Q(shi)} / 2 ^ 53)) (by
      rw [abs_of_pos (by linarith)]
      linarith) (by norm_num)
  have hsw0 : {Q(mb)} ≤ |vs + vw| := by
    rw [abs_of_pos (by linarith)]
    have : ({Q(mb)} : ℝ) ≤ ({Q(slo)} - {Q(shi)} / 2 ^ 53) + {Q(VWLO)} := by norm_num
    linarith
  have hc := fapprox_div htwA hsw {Q(Mtw)} {Q(mb)} htw0 hsw0 (by norm_num) {Q(Bc)} (by norm_num)
    (by norm_num)
  set cv := (vt - vw * vw) / (vs + vw) with hcv
  have hcM : |cv| ≤ {Q(Mc)} := by
    rw [hcv, abs_div]
    calc |vt - vw * vw| / |vs + vw| ≤ {Q(Mtw)} / |vs + vw| :=
          div_le_div_of_nonneg_right htw0 (abs_nonneg _)
      _ ≤ {Q(Mtw)} / {Q(mb)} := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsw0
      _ ≤ {Q(Mc)} := by norm_num
  have h2f : FApprox (2.0 : Float) 2 0 := by
    have := Log1pTheoremCore.two_approx.approx
    rw [zero_mul] at this
    exact this
  have hc2 := fapprox_mul h2f hc 2 {Q(Mc)} (by norm_num) hcM {Q(Bc2)} (by norm_num) (by norm_num)
  have hlof : Finite (0x3C91A62633145C07 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hh4f : Finite (0x3FE921FB54442D18 : UInt64) := by
    unfold CodeLib.IEEE64.Finite; decide +kernel
  have hlov : |value (0x3C91A62633145C07 : UInt64)| ≤ 1 / 10 ^ 16 :=
    le_trans (abs_value_le _ ((1 / 10 ^ 16 : ℚ)) (by decide +kernel)) (by norm_num)
  have h4v : |value (0x3FE921FB54442D18 : UInt64) - 7853981633974483 / 10 ^ 16| ≤ 1 / 10 ^ 16 := by
    rw [← ratOfWord_cast]
    have h := qabs_cast (ratOfWord 0x3FE921FB54442D18 - 7853981633974483 / 10 ^ 16)
    push_cast at h
    rw [← h]
    exact_mod_cast (by decide +kernel :
      qabs (ratOfWord 0x3FE921FB54442D18 - 7853981633974483 / 10 ^ 16) ≤ 1 / 10 ^ 16)
  have hlo2c := fapprox_sub (const_word _ hlof) hc2 {Q(Blo)} (by
    have h3 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h3
    norm_num at h3 hcM hlov ⊢
    linarith) (by norm_num)
  -- `2 s r`
  obtain ⟨h2sf, h2sv⟩ := AtanTheoremReduce.double_float s hs.1 (by
      rw [abs_of_pos hvs0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ {Q(slo)} - {Q(shi)} / 2 ^ 53 := by norm_num
      linarith) (by
      rw [abs_of_pos hvs0]
      have : ({Q(shi)} : ℝ) + {Q(shi)} / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hs2 : FApprox (2.0 * s) (2 * Real.sqrt vt) (2 * ({Q(shi)} / 2 ^ 53)) := by
    refine ⟨h2sf, ?_⟩
    rw [h2sv, show 2 * vs - 2 * Real.sqrt vt = 2 * (vs - Real.sqrt vt) by ring, abs_mul, abs_two]
    have := hs.2
    linarith
  have hsr := fapprox_mul hs2 hrA' (2 * {Q(shi)}) {Q(MrA)} (by
      rw [abs_mul, abs_two, abs_of_pos hsqrt0]; linarith) hrM' {Q(Bsr)} (by norm_num)
    (by norm_num)
  have hp := fapprox_sub_half hsr hlo2c {gp} (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * {Q(shi)} * {Q(MrA)} := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    norm_num at h3 h4 h5 hcM hlov ⊢
    linarith)
  -- `q = π/4 - 2 w`
  obtain ⟨h2wf, h2wv⟩ := AtanTheoremReduce.double_float w hwf (by
      rw [abs_of_pos hvw0]
      have : (1 : ℝ) / 2 ^ 1000 ≤ {Q(VWLO)} := by norm_num
      linarith) (by
      rw [abs_of_pos hvw0]
      have : ({Q(shi)} : ℝ) + {Q(shi)} / 2 ^ 53 < 2 ^ 900 := by norm_num
      linarith)
  have hw2 : FApprox (2.0 * w) (2 * vw) 0 := ⟨h2wf, by rw [h2wv, sub_self, abs_zero]⟩
  have hqb : |value (0x3FE921FB54442D18 : UInt64) - 2 * vw| ≤ {Q(Mq)} := by
    rw [abs_le]
    obtain ⟨h5, h6⟩ := abs_le.mp h4v
    constructor <;> norm_num at h5 h6 hvwlo hvwhi ⊢ <;> linarith
  have hq := fapprox_sub_half (const_word _ hh4f) hw2 {gq} (by norm_num) (by
    norm_num at hqb ⊢
    linarith)
  have hpq := fapprox_sub_half hp hq {gpq} (by norm_num) (by
    have h3 := abs_sub (2 * Real.sqrt vt * rv - (value (0x3C91A62633145C07 : UInt64) - 2 * cv))
      (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)
    have h4 : |2 * Real.sqrt vt * rv| ≤ 2 * {Q(shi)} * {Q(MrA)} := by
      rw [abs_mul, abs_mul, abs_two, abs_of_pos hsqrt0]
      exact mul_le_mul (by linarith) hrM' (abs_nonneg _) (by norm_num)
    have h5 := abs_sub (value (0x3C91A62633145C07 : UInt64)) (2 * cv)
    rw [abs_mul, abs_two] at h5
    have h6 := abs_sub (2 * Real.sqrt vt * rv) (value (0x3C91A62633145C07 : UInt64) - 2 * cv)
    norm_num at h3 h4 h5 h6 hcM hlov hqb ⊢
    linarith)
  -- the exact value against `arcsin a`
  have hy0 := arcsin_half a (by linarith) (by linarith)
  rw [← hvt] at hy0
  have hker := asin_kernel (Real.sqrt vt) (by rw [abs_of_pos hsqrt0]; linarith)
  rw [hsqv, abs_of_pos hsqrt0] at hker
  have hpi := AtanTheoremConst.atan_inf
  have hh4 : value (0x3FE921FB54442D18 : UInt64) + value (0x3FE921FB54442D18 : UInt64) =
      value (0x3FF921FB54442D18 : UInt64) := by
    rw [← ratOfWord_cast, ← ratOfWord_cast, ← ratOfWord_cast]
    exact_mod_cast (by decide +kernel : ratOfWord 0x3FE921FB54442D18 +
      ratOfWord 0x3FE921FB54442D18 = ratOfWord 0x3FF921FB54442D18)
  have hk3 : Real.sqrt vt ^ 3 ≤ {Q(shi)} ^ 3 := pow_le_pow_left₀ hsqrt0.le hsqhi 3
  have hsm : |Real.sqrt vt - vw - cv| ≤ {Q(small)} := by
    have hden1 : 0 < Real.sqrt vt + vw := by linarith
    have hden2 : 0 < vs + vw := by linarith
    have hid : Real.sqrt vt - vw - cv = (vt - vw * vw) * (vs - Real.sqrt vt) /
        ((Real.sqrt vt + vw) * (vs + vw)) := by
      rw [hcv]
      field_simp
      rw [← hsqv]
      ring
    rw [hid, abs_div, abs_mul, abs_of_pos (mul_pos hden1 hden2)]
    have h3 : |vs - Real.sqrt vt| ≤ {Q(shi)} / 2 ^ 53 := hs.2
    have h4 : ({Q(mbp)} : ℝ) * {Q(mb)} ≤ (Real.sqrt vt + vw) * (vs + vw) := by
      apply mul_le_mul _ _ (by norm_num) (by linarith)
      · have : ({Q(mbp)} : ℝ) ≤ {Q(slo)} + {Q(VWLO)} := by norm_num
        linarith
      · have : ({Q(mb)} : ℝ) ≤ ({Q(slo)} - {Q(shi)} / 2 ^ 53) + {Q(VWLO)} := by norm_num
        linarith
    rw [div_le_iff₀ (mul_pos hden1 hden2)]
    have h5 := mul_le_mul htw0 h3 (abs_nonneg _) (by norm_num)
    have h6 : ({Q(Mtw)} : ℝ) * ({Q(shi)} / 2 ^ 53) ≤ {Q(small)} * ({Q(mbp)} * {Q(mb)}) := by
      norm_num
    nlinarith
  have hd : |value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) - Real.arcsin a| ≤
      1 / 2 ^ 64 + 2 * ({Q(shi)} ^ 3 * ((11 / 16) / 2 ^ 56)) + 2 * {Q(small)} := by
    rw [hy0, show value (0x3FE921FB54442D18 : UInt64) - ((2 * Real.sqrt vt * rv -
      (value (0x3C91A62633145C07 : UInt64) - 2 * cv)) -
        (value (0x3FE921FB54442D18 : UInt64) - 2 * vw)) -
          (Real.pi / 2 - 2 * Real.arcsin (Real.sqrt vt)) =
        (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
          2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
            eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))) +
          2 * (Real.sqrt vt - vw - cv) by rw [← hh4, hrv]; ring]
    have h3 := abs_add_le ((value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2) +
      2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt)))) (2 * (Real.sqrt vt - vw - cv))
    have h4 := abs_add_le (value 0x3FF921FB54442D18 + value 0x3C91A62633145C07 - Real.pi / 2)
      (2 * (Real.arcsin (Real.sqrt vt) - (Real.sqrt vt + Real.sqrt vt * (vt *
        eval AsinKernelPoly.asinP vt / eval AsinKernelPoly.asinQ vt))))
    rw [abs_mul, abs_two] at h3 h4
    have h5 : Real.sqrt vt ^ 3 * ((11 / 16) / 2 ^ 56) ≤ {Q(shi)} ^ 3 * ((11 / 16) / 2 ^ 56) :=
      mul_le_mul_of_nonneg_right hk3 (by positivity)
    linarith
  have hB : value (UInt64.ofNat ({n} * 2 ^ 52)) = {"1" if n==1023 else "1 / 2"} := by
    rw [F64PositiveSpacing.boundary_value {n} (by norm_num) (by norm_num)]
    norm_num
  have hyt := abs_arcsin_lt a
  refine sub_within (const_word _ hh4f) hpq (Real.arcsin a) {Q(Enum)} ?_ {n} (by norm_num)
    (by norm_num) ?_ (by norm_num) (lt_trans hyt (by norm_num))
  · norm_num at hd ⊢
    linarith
  · rw [hB, abs_of_pos (by linarith)]
    linarith
'''
out=open('../AsinTheoremMid.lean','w')
out.write('''import Verified.Examples.AsinTheoremBig

/-!
`Asin.asin x` for `1/2 ≤ |x| < 0.975`: with `t = (1 - |x|)/2`, `s = √t`, `w` the high part of
`s`, and `c = (t - w²)/(s + w)`, the code computes `π/4 - (p - q)` with
`p = 2 s r - (pio2_lo - 2c)` and `q = π/4 - 2w`.  Its exact value is `π/2 - 2 (w + c) - 2 √t r`
up to the constants, and `w + c` lies within `2 ^ -70` of `√t`.  The three ranges of `|x|` use the
chains `A1`, `A2`, and `A3` of `AsinTheoremRatio`.
-/

namespace Verified.Examples.AsinTheoremMid
open CodeLib.IEEE64 LeanExe.ProofKit F64Approx F64RoundNearest F64HalfUlp PolyBound
  AsinTheoremSupport AsinTheoremRatio AsinTheoremBranches AsinTheoremSmall AsinTheoremHalf
  AsinTheoremBig

set_option exponentiation.threshold 4096
''')
out.write(emit("A",F(1,2),F(6,10),("A1",F(1,5),F(1,4)),1022,F(196,100)*U54))
out.write(emit("B",F(6,10),F(9,10),("A2",F(1,20),F(1,5)),1022,F(196,100)*U54))
out.write(emit("C",F(9,10),F(975,1000),("A3",F(1,80),F(1,20)),1023,F(25,10)*U54))
out.write("\nend Verified.Examples.AsinTheoremMid\n")
out.close()
