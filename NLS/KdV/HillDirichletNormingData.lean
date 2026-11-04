import NLS.KdV.HillDirichletLabelContinuity
import NLS.KdV.HillDirichletSlope

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem hillL2DirichletSlope_signed_pos
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) (x : ℝ)
    (hx : x∈Icc (hillRealLabels q hq hr (2*n-1)) (hillRealLabels q hq hr (2*n)))
    (hz : hillL2DirichletCharacteristic (SpectralWeight.one.toCoeff q) x=0) :
    0<(-1 : ℝ)^n*(hillL2DirichletSlope (SpectralWeight.one.toCoeff q) x).re := by
  let p := SpectralWeight.one.toCoeff q
  let s : ℝ := (-1)^n
  let d := (deriv (hillL2DirichletCharacteristic p) x).re
  let g := (hillL2DirichletSlope p x).re
  have hd : 0<s*d := hillL2DirichletCharacteristic_signed_deriv_pos q hq hr n hn x hx hz
  have hs : s^2=1 := by dsimp [s];rw [← pow_mul,Nat.mul_comm n 2,pow_mul];norm_num
  have he : deriv (hillL2DirichletCharacteristic p) x*hillL2DirichletSlope p x=
      (NLS.ComplexAnalysis.scalarStateMass (hillL2FrequencyStateCurve p (Complex.sqrt x) (0,1)) : ℂ) :=
    hillL2Dirichlet_derivative_normalization p hr x hz
  have hn' : d*g=NLS.ComplexAnalysis.scalarStateMass (hillL2FrequencyStateCurve p (Complex.sqrt x) (0,1)) := by
    simpa only [mul_re,hillL2DirichletSlope_real p hr x,mul_zero,sub_zero,ofReal_re] using congrArg Complex.re he
  have hm := hillL2FrequencyStateCurve_mass_pos p (Complex.sqrt x) (0,1)
    (by intro h;have hh := congrArg Prod.snd h;norm_num at hh)
  change 0<s*g
  have hid : (s*d)*(s*g)=d*g := by calc
    _ = s^2*(d*g) := by ring
    _ = d*g := by rw [hs,one_mul]
  have hp : 0<(s*d)*(s*g) := by rw [hid,hn'];exact hm
  exact pos_of_mul_pos_right hp hd.le

def hillDirichletMultiplier
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) : ℝ :=
  (-1 : ℝ)^n*(hillL2DirichletSlope (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)).re

theorem hillDirichletMultiplier_pos
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    0<hillDirichletMultiplier q hq hr n hn :=
  hillL2DirichletSlope_signed_pos q hq hr n hn _
    (hillDirichletEnergy_mem_gap q hq hr n hn) (hillDirichletEnergy_zero q hq hr n hn)

def hillDirichletLogMultiplier
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) : ℝ :=
  Real.log (hillDirichletMultiplier q hq hr n hn)

theorem continuous_hillDirichletMultiplier (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletMultiplier q.val q.property.1 q.property.2 n hn) := by
  have hc : Continuous (fun p : ℂ × Coeff 2 => hillL2DirichletSlope p.2 p.1) :=
    continuous_iff_continuousAt.mpr (fun p =>
      (analyticOnNhd_hillL2DirichletSlope_joint p (mem_univ _)).continuousAt)
  have hm : Continuous (fun q : RealPeriodOneHillPotential =>
      ((hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ),SpectralWeight.one.toCoeff q.val)) :=
    (Complex.continuous_ofReal.comp (continuous_hillDirichletEnergy n hn)).prodMk
      (SpectralWeight.one.toCoeff.continuous.comp continuous_subtype_val)
  have he : Continuous (fun q : RealPeriodOneHillPotential =>
      (hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
        (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)).re) := by
    convert! Complex.continuous_re.comp (hc.comp hm) using 1
  exact continuous_const.mul he

theorem continuous_hillDirichletLogMultiplier (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletLogMultiplier q.val q.property.1 q.property.2 n hn) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  have hm : ContinuousAt (fun p : RealPeriodOneHillPotential =>
      hillDirichletMultiplier p.val p.property.1 p.property.2 n hn) q :=
    (continuous_hillDirichletMultiplier n hn).continuousAt
  have hc := (Real.continuousAt_log (hillDirichletMultiplier_pos q.val q.property.1 q.property.2 n hn).ne').comp
    (f := fun p : RealPeriodOneHillPotential => hillDirichletMultiplier p.val p.property.1 p.property.2 n hn) hm
  convert! hc using 1

theorem hillDirichletMultiplier_trace
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    hillDirichletMultiplier q hq hr n hn+1/hillDirichletMultiplier q hq hr n hn=
      (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)).re := by
  let p := SpectralWeight.one.toCoeff q
  let x := hillDirichletEnergy q hq hr n hn
  let z := Complex.sqrt (x : ℂ)
  let t : Icc (0 : ℝ) 1 := ⟨1,by norm_num⟩
  let c := (hillL2FrequencyStateCurve p z (1,0) t).1.re
  let g := (hillL2DirichletSlope p x).re
  let s : ℝ := (-1)^n
  let a := hillDirichletMultiplier q hq hr n hn
  have ha : 0<a := hillDirichletMultiplier_pos q hq hr n hn
  have hs : s^2=1 := by dsimp [s];rw [← pow_mul,Nat.mul_comm n 2,pow_mul];norm_num
  have he : z^2=(x : ℂ) := complex_sqrt_sq _
  have hzero : (hillL2FrequencyStateCurve p z (0,1) t).1=0 := hillDirichletEnergy_zero q hq hr n hn
  have hw := hillL2FrequencyStateCurve_wronskian p z t
  rw [hzero,zero_mul,sub_zero] at hw
  have hprod : c*g=1 := by
    have hh := congrArg Complex.re hw
    change c*g-(hillL2FrequencyStateCurve p z (1,0) t).1.im*(hillL2DirichletSlope p x).im=1 at hh
    simpa only [hillL2DirichletSlope_real p hr x,mul_zero,sub_zero] using hh
  have htrace : c+g=(hillL2Discriminant p x).re := by
    have ht := congrArg Complex.re (hillL2FrequencyStateCurve_trace p z)
    rw [← hillL2Discriminant_sq,he] at ht
    exact ht
  have hi : (s*c)*a=1 := by
    change (s*c)*(s*g)=1
    calc
      _ = s^2*(c*g) := by ring
      _ = 1 := by rw [hs,hprod];norm_num
  have hi' : 1/a=s*c := ((eq_div_iff ha.ne').mpr hi).symm
  change a+1/a=s*(hillL2Discriminant p x).re
  rw [hi',← htrace]
  change s*g+s*c=s*(c+g)
  ring

theorem hillDirichletLogMultiplier_cosh
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    Real.cosh (hillDirichletLogMultiplier q hq hr n hn)=
      ((-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)).re)/2 := by
  rw [hillDirichletLogMultiplier,Real.cosh_eq,Real.exp_neg,
    Real.exp_log (hillDirichletMultiplier_pos q hq hr n hn)]
  simpa only [one_div] using congrArg (fun x : ℝ => x/2) (hillDirichletMultiplier_trace q hq hr n hn)

theorem hillDirichletLogMultiplier_eq_zero_iff
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    hillDirichletLogMultiplier q hq hr n hn=0 ↔
      (-1 : ℝ)^n*(hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)).re=2 := by
  let A := hillDirichletMultiplier q hq hr n hn
  have hp : 0<A := hillDirichletMultiplier_pos q hq hr n hn
  have ht := hillDirichletMultiplier_trace q hq hr n hn
  change A+1/A=_ at ht
  constructor
  · intro hk
    have ha : A=1 := by
      have hh := congrArg Real.exp hk
      change Real.exp (Real.log A)=Real.exp 0 at hh
      simpa only [Real.exp_log hp,Real.exp_zero] using hh
    rw [ha] at ht
    norm_num at ht
    exact ht.symm
  · intro he
    rw [he] at ht
    have hm := congrArg (fun z : ℝ => z*A) ht
    rw [add_mul,div_mul_cancel₀ _ hp.ne'] at hm
    have ha : A=1 := by nlinarith [sq_nonneg (A-1)]
    change Real.log A=0
    rw [ha,Real.log_one]

theorem hillDirichletLogMultiplier_eq_zero_of_closed_gap
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n)
    (hc : hillRealLabels q hq hr (2*n-1)=hillRealLabels q hq hr (2*n)) :
    hillDirichletLogMultiplier q hq hr n hn=0 := by
  apply (hillDirichletLogMultiplier_eq_zero_iff q hq hr n hn).mpr
  have hm := hillDirichletEnergy_mem_gap q hq hr n hn
  have he : hillDirichletEnergy q hq hr n hn=hillRealLabels q hq hr (2*n-1) := by
    rw [← hc] at hm
    exact le_antisymm hm.2 hm.1
  rw [he]
  exact (hillRealLabels_signed_pair_trace q hq hr n hn).1

theorem hillDirichletLogMultiplier_zero_potential
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))
    (n : ℕ) (hn : 1≤n) : hillDirichletLogMultiplier 0 hq hr n hn=0 := by
  apply hillDirichletLogMultiplier_eq_zero_of_closed_gap 0 hq hr n hn
  rw [hillRealLabels_zero,hillRealLabels_zero]
  congr 1
  omega

theorem hillDirichletLogMultiplier_eq_zero_iff_endpoint
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    hillDirichletLogMultiplier q hq hr n hn=0 ↔
      hillDirichletEnergy q hq hr n hn=hillRealLabels q hq hr (2*n-1) ∨
      hillDirichletEnergy q hq hr n hn=hillRealLabels q hq hr (2*n) := by
  have hm := hillDirichletEnergy_mem_gap q hq hr n hn
  rw [hillDirichletLogMultiplier_eq_zero_iff]
  constructor
  · intro he
    by_contra! hh
    have hg := hillL2Discriminant_signed_gap_gt_two q hq hr n hn _
      ⟨lt_of_le_of_ne hm.1 (Ne.symm hh.1),lt_of_le_of_ne hm.2 hh.2⟩
    linarith
  · rintro (he | he)
    · rw [he];exact (hillRealLabels_signed_pair_trace q hq hr n hn).1
    · rw [he];exact (hillRealLabels_signed_pair_trace q hq hr n hn).2

theorem hillDirichletLogMultiplier_sinh_sq
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (n : ℕ) (hn : 1≤n) :
    (2*Real.sinh (hillDirichletLogMultiplier q hq hr n hn))^2=
      (hillL2Discriminant (SpectralWeight.one.toCoeff q) (hillDirichletEnergy q hq hr n hn)).re^2-4 := by
  have hs : ((-1 : ℝ)^n)^2=1 := by rw [← pow_mul,Nat.mul_comm n 2,pow_mul];norm_num
  have hc := congrArg (fun x : ℝ => x^2) (hillDirichletLogMultiplier_cosh q hq hr n hn)
  simp only [div_pow,mul_pow,hs,one_mul] at hc
  nlinarith [Real.cosh_sq_sub_sinh_sq (hillDirichletLogMultiplier q hq hr n hn)]

end NLS.KdV
