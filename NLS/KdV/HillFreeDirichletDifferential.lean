import NLS.KdV.HillFreeCoordinateNormalization
import NLS.KdV.HillFreeSpectralVariations
/-! # Actual free Dirichlet variations and the Fourier pairing -/
noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.Fourier
namespace NLS.KdV

theorem hillL2DirichletCharacteristic_free (E : ℂ) (hE : E≠0) :
    hillL2DirichletCharacteristic 0 E=sin (Complex.sqrt E)/Complex.sqrt E := by
  have hz : Complex.sqrt E≠0 := by
    intro hz
    have hs := complex_sqrt_sq E
    rw [hz,zero_pow (by norm_num : (2:ℕ)≠0)] at hs
    exact hE hs.symm
  simpa only [complex_sqrt_sq] using hillL2DirichletCharacteristic_free_sq (Complex.sqrt E) hz

theorem deriv_hillL2DirichletCharacteristic_free_center (n : ℕ) (hn : 1≤n) :
    deriv (hillL2DirichletCharacteristic 0) (freeHillValue n)=
      (-1:ℂ)^n/(2*((n:ℂ)*Real.pi)^2) := by
  let ν : ℕ+ := ⟨n,by omega⟩
  let a : ℂ := freeHillValue n
  have he : freeHillEnergy ν=a := by
    change (((((n:ℝ)*Real.pi)^2):ℝ):ℂ)=((Real.pi^2*(n:ℝ)^2:ℝ):ℂ)
    push_cast
    ring
  have ha : a∈slitPlane := he ▸ freeHillEnergy_mem_slitPlane ν
  have ha0 : a≠0 := slitPlane_ne_zero ha
  have hz : Complex.sqrt a≠0 := by
    rw [← he,sqrt_freeHillEnergy]
    exact mul_ne_zero (by exact_mod_cast ν.ne_zero) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hexp : a^(-1/2:ℂ)=(Complex.sqrt a)⁻¹ := by
    rw [show (-1/2:ℂ)=-(2⁻¹) by norm_num,Complex.cpow_neg]
    rfl
  have hs : HasDerivAt Complex.sqrt ((Complex.sqrt a)⁻¹/2) a := by
    simpa only [hexp] using Complex.hasDerivAt_sqrt ha
  have hd := hs.csin.div hs hz
  have heq : hillL2DirichletCharacteristic 0 =ᶠ[𝓝 a]
      (fun E => sin (Complex.sqrt E)/Complex.sqrt E) := by
    filter_upwards [eventually_ne_nhds ha0] with E hE
    exact hillL2DirichletCharacteristic_free E hE
  have hcos : cos ((n:ℂ)*Real.pi)=(-1:ℂ)^n := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    push_cast at h
    exact h
  rw [(hd.congr_of_eventuallyEq heq).deriv]
  dsimp only [a]
  rw [hillFreeGap_sqrt,Complex.sin_nat_mul_pi,hcos]
  change _=(-1:ℂ)^n/(2*((n:ℂ)*Real.pi)^2)
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hpi : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hn0,hpi]
  ring

variable
    (hq : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem scalarStateMass_hill_free_center (n : ℕ) (hn : 1≤n) :
    (scalarStateMass (hillL2FrequencyStateCurve 0 (Complex.sqrt (freeHillValue n)) (0,1)):ℂ)=
      (2*((n:ℂ)*Real.pi)^2)⁻¹ := by
  have hreal : IsRealHillPotential (0:Coeff 2) := by intro k;simp
  have hzero : hillL2DirichletCharacteristic 0 (freeHillValue n)=0 := by
    have h := hillL2DirichletCharacteristic_free_nat_root n hn
    convert h using 1
    simp only [freeHillValue,ofReal_mul,ofReal_pow]
    push_cast
    ring
  have hm := hillL2Dirichlet_derivative_normalization 0 hreal (freeHillValue n) hzero
  change deriv (hillL2DirichletCharacteristic 0) (freeHillValue n)*
    hillL2DirichletSlope 0 (freeHillValue n)=_ at hm
  have hcos : cos ((n:ℂ)*Real.pi)=(-1:ℂ)^n := by
    have h := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    push_cast at h
    exact h
  rw [deriv_hillL2DirichletCharacteristic_free_center n hn,hillL2DirichletSlope_free,
    hillFreeGap_sqrt,hcos] at hm
  rw [hillFreeGap_sqrt,← hm]
  have hs : ((-1:ℂ)^n)^2=1 := by rw [← pow_mul,Nat.mul_comm n 2,pow_mul];norm_num
  have hn0 : (n:ℂ)≠0 := by exact_mod_cast (by omega : n≠0)
  have hpi : (Real.pi:ℂ)≠0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp [hn0,hpi]
  linear_combination hs

theorem hillDirichlet_branch_fderiv_free_integral
    (n : ℕ) (hn : 1≤n) (μ : Coeff 2 → ℂ) (hμ : AnalyticAt ℂ μ 0)
    (hμ0 : μ 0=(freeHillValue n:ℂ))
    (hz : ∀ᶠ p in 𝓝 (0:Coeff 2), hillL2DirichletCharacteristic p (μ p)=0) (h : Coeff 2) :
    (fderiv ℂ μ 0) h=2*(∫ x in (0:ℝ)..1,
      -(hillPhysicalDirection h).ofLp.2 x*sin ((n:ℂ)*Real.pi*x)^2) := by
  have hreal : IsRealHillPotential (0:Coeff 2) := by intro k;simp
  have hd := hillDirichlet_branch_fderiv_integral 0 hreal μ hμ hz h
  rw [hμ0,scalarStateMass_hill_free_center n hn,hillFreeGap_sqrt] at hd
  let k : ℂ := (n:ℂ)*Real.pi
  have hk : k≠0 := mul_ne_zero (by exact_mod_cast (by omega : n≠0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hi : (∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
      (extend (hillL2FrequencyStateCurve 0 k (0,1)) x).1^2)=
      (1/k^2)*(∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*sin (k*x)^2) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxi : x∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hxi,hillL2FrequencyStateCurve_free_sine k hk]
    field_simp
  change (fderiv ℂ μ 0) h=(∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
    (extend (hillL2FrequencyStateCurve 0 k (0,1)) x).1^2)/(2*k^2)⁻¹ at hd
  rw [hi] at hd
  have hc (J : ℂ) : (1/k^2*J)/(2*k^2)⁻¹=2*J := by field_simp [hk]
  rw [hc] at hd
  exact hd

theorem fderiv_hillL2DirichletSlope_free_integral (n : ℕ) (hn : 1≤n) (h : Coeff 2) :
    (fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p (freeHillValue n)) 0) h=
      (-1:ℂ)^n/((n:ℂ)*Real.pi)*(∫ x in (0:ℝ)..1,
        -(hillPhysicalDirection h).ofLp.2 x*cos ((n:ℂ)*Real.pi*x)*sin ((n:ℂ)*Real.pi*x)) := by
  let k : ℂ := (n:ℂ)*Real.pi
  have hk : k≠0 := mul_ne_zero (by exact_mod_cast (by omega : n≠0)) (ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcos : cos ((n:ℂ)*Real.pi)=(-1:ℂ)^n := by
    have hh := congrArg Complex.ofReal (Real.cos_nat_mul_pi n)
    push_cast at hh
    exact hh
  rw [fderiv_hillL2DirichletSlope_integral,hillFreeGap_sqrt,
    hillL2FrequencyStateCurve_free_cosine,hillL2DirichletSlope_free,hillFreeGap_sqrt,hcos]
  simp only [ofReal_one,mul_one,Complex.sin_nat_mul_pi,mul_zero,neg_zero,zero_mul,zero_add]
  have hi : (∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
      (extend (hillL2FrequencyStateCurve 0 k (1,0)) x).1*
      (extend (hillL2FrequencyStateCurve 0 k (0,1)) x).1)=
      (1/k)*(∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*cos (k*x)*sin (k*x)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxi : x∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ hxi,hillL2FrequencyStateCurve_free_cosine,
      hillL2FrequencyStateCurve_free_sine k hk]
    ring
  rw [hi]
  dsimp only [k]
  ring

theorem intervalIntegrable_hillPhysicalDirection_mul_continuous (h : Coeff 2)
    (f : ℝ → ℂ) (hf : Continuous f) :
    IntervalIntegrable (fun x => -(hillPhysicalDirection h).ofLp.2 x*f x) volume 0 1 := by
  let F : Curve ℂ := ⟨fun t => f t,hf.comp continuous_subtype_val⟩
  have hi := (intervalIntegrable_intervalL2_mul (hillPhysicalDirection h).ofLp.2
    (curveBoundedExtension ℂ F) ⟨1,by norm_num⟩).neg
  apply hi.congr_ae
  rw [uIoc_of_le (by norm_num : (0:ℝ)≤1)]
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hxi : x∈Icc (0:ℝ) 1 := ⟨hx.1.le,hx.2⟩
  simp only [Pi.neg_apply,curveBoundedExtension_apply,NLS.LinearVolterra.extend,
    F,ContinuousMap.coe_mk,projIcc_of_mem _ hxi]
  ring

theorem hillFreeDirichlet_fourier_pairing (n : ℕ) (h : Coeff 2)
    (hh : h∈Coeff.paritySubspace 0) (hm : h 0=0) :
    -2*I*(∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
      cos ((n:ℂ)*Real.pi*x)*sin ((n:ℂ)*Real.pi*x))-
    2*(∫ x in (0:ℝ)..1, -(hillPhysicalDirection h).ofLp.2 x*
      sin ((n:ℂ)*Real.pi*x)^2)=h (2*(n:ℤ)) := by
  let k : ℂ := (n:ℂ)*Real.pi
  let H : ℝ → ℂ := fun x => -(hillPhysicalDirection h).ofLp.2 x
  have hmean : (∫ x in (0:ℝ)..1,H x)=0 := integral_hillPhysicalDirection_eq_zero_of_even h hh hm
  have hpoint (x : ℝ) : wave (2*(-(n:ℤ))) x-1=
      -2*I*cos (k*x)*sin (k*x)-2*sin (k*x)^2 := by
    have ha : ((Real.pi:ℂ)*I*(((2*(-(n:ℤ)):ℤ):ℂ)))*x=(-(k*x)*I)+(-(k*x)*I) := by
      dsimp only [k]
      push_cast
      ring
    rw [wave,ha,exp_add,exp_mul_I]
    simp only [cos_neg,sin_neg]
    ring_nf
    rw [I_sq]
    linear_combination sin_sq_add_cos_sq (k*x)
  have hp := hillPhysicalCurvePairing_unitWaveCurve_even h hh (n:ℤ)
  rw [hillPhysicalCurvePairing_apply] at hp
  have hp' : (∫ x in (0:ℝ)..1,H x*wave (2*(-(n:ℤ))) x)=h (2*(n:ℤ)) := by
    rw [← hp]
    apply intervalIntegral.integral_congr
    intro x hx
    have hxi : x∈Icc (0:ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0:ℝ)≤1)] using hx
    dsimp only
    rw [extend_unitWaveCurve_of_mem _ hxi]
    dsimp only [H]
    ring
  have hcs := intervalIntegrable_hillPhysicalDirection_mul_continuous h
    (fun x : ℝ => cos (k*x)*sin (k*x)) (by fun_prop)
  have hcs' : IntervalIntegrable (fun x : ℝ => H x*cos (k*x)*sin (k*x)) volume 0 1 := by
    convert hcs using 1
    funext x
    dsimp only [H]
    ring
  have hss := intervalIntegrable_hillPhysicalDirection_mul_continuous h
    (fun x : ℝ => sin (k*x)^2) (by fun_prop)
  have hw := intervalIntegrable_hillPhysicalDirection_mul_continuous h
    (wave (2*(-(n:ℤ)))) (continuous_wave _)
  have h1 := intervalIntegrable_hillPhysicalDirection_mul_continuous h
    (fun _ : ℝ => (1:ℂ)) continuous_const
  simp only [mul_one] at h1
  calc
    _ = ∫ x in (0:ℝ)..1, H x*(-2*I*cos (k*x)*sin (k*x)-2*sin (k*x)^2) := by
      rw [← intervalIntegral.integral_const_mul,← intervalIntegral.integral_const_mul,
        ← intervalIntegral.integral_sub (hcs'.const_mul (-2*I)) (hss.const_mul 2)]
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only [H,k]
      ring
    _ = ∫ x in (0:ℝ)..1,H x*(wave (2*(-(n:ℤ))) x-1) := by
      apply intervalIntegral.integral_congr
      intro x _hx
      dsimp only
      rw [hpoint]
    _ = (∫ x in (0:ℝ)..1,H x*wave (2*(-(n:ℤ))) x)-(∫ x in (0:ℝ)..1,H x) := by
      simp only [mul_sub,mul_one]
      exact intervalIntegral.integral_sub hw h1
    _ = h (2*(n:ℤ)) := by rw [hp',hmean,sub_zero]
end NLS.KdV
