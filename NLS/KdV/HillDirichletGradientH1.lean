import NLS.KdV.HillDirichletGardnerBrackets

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ComplexConjugate ENNReal

namespace NLS.KdV

theorem hillDirichletGradient_H1
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmem (w : Curve ℂ) : MemLp (NLS.LinearVolterra.extend w) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_extend w).aestronglyMeasurable).mpr
      (((continuous_extend w).norm.pow 2).intervalIntegrable 0 1).1
  refine ⟨absolutelyContinuousOnInterval_hillDirichletGradientCurve q n hn,hmem _,?_⟩
  apply (hmem (hillDirichletGradientSpatialCurve q n hn)).ae_eq
  filter_upwards [ae_hasDerivAt_hillDirichletGradientCurve q n hn] with x hx
  exact hx.deriv.symm

theorem hillDirichletGradient_integral_eq_one
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    (∫ x in (0 : ℝ)..1, NLS.LinearVolterra.extend (hillDirichletGradientCurve q n hn) x)=1 := by
  let A := hillDirichletStateCurve q n hn
  let M := scalarStateMass A
  have hp : 0<M := hillL2FrequencyStateCurve_mass_pos (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
    (by intro hh;have hh' := congrArg Prod.snd hh;norm_num at hh')
  have hr (t : Icc (0 : ℝ) 1) : (A t).1.im=0 := by
    exact (hillL2FrequencyStateCurve_real (SpectralWeight.one.toCoeff q.val) q.property.2 _
      (by rw [complex_sqrt_sq];rfl) (0,1) (by norm_num) t).1
  have hc := scalarStateCrossMass_self_real A hr
  rw [scalarStateCrossMass_eq_integral] at hc
  have hi : (∫ x in (0 : ℝ)..1,(NLS.LinearVolterra.extend A x).1^2)=(M : ℂ) := by
    simpa only [pow_two] using hc
  change (∫ x in (0 : ℝ)..1,(M : ℂ)⁻¹*(NLS.LinearVolterra.extend A x).1^2)=1
  rw [intervalIntegral.integral_const_mul,hi,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne')]

theorem hillDirichletState_mass_pos
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) :
    0<scalarStateMass (hillDirichletStateCurve q n hn) :=
  hillL2FrequencyStateCurve_mass_pos (SpectralWeight.one.toCoeff q.val)
    (Complex.sqrt (hillDirichletEnergy q.val q.property.1 q.property.2 n hn)) (0,1)
    (by intro hh;have hh' := congrArg Prod.snd hh;norm_num at hh')

theorem continuous_hillDirichletGradientCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletGradientCurve q n hn) := by
  have hA := continuous_hillDirichletStateCurve n hn
  have hM : Continuous (fun q : RealPeriodOneHillPotential =>
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹) :=
    (Complex.continuous_ofReal.comp (continuous_scalarStateMass.comp hA)).inv₀
      (fun q => Complex.ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne')
  exact hM.smul (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hA).pow 2)

theorem continuous_hillDirichletGradientSpatialCurve (n : ℕ) (hn : 1≤n) :
    Continuous (fun q : RealPeriodOneHillPotential => hillDirichletGradientSpatialCurve q n hn) := by
  have hA := continuous_hillDirichletStateCurve n hn
  have hM : Continuous (fun q : RealPeriodOneHillPotential =>
      2/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)) :=
    continuous_const.div (Complex.continuous_ofReal.comp (continuous_scalarStateMass.comp hA))
      (fun q => Complex.ofReal_ne_zero.mpr (hillDirichletState_mass_pos q n hn).ne')
  exact hM.smul (((ContinuousMap.fst : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hA).mul
    ((ContinuousMap.snd : C(ℂ × ℂ,ℂ)).continuous_postcomp.comp hA))

theorem hillDirichletGradientCurve_real
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1≤n) (t : Icc (0 : ℝ) 1) :
    (hillDirichletGradientCurve q n hn t).im=0 := by
  let A := hillDirichletStateCurve q n hn
  have hr : (A t).1.im=0 :=
    (hillL2FrequencyStateCurve_real (SpectralWeight.one.toCoeff q.val) q.property.2 _
      (by rw [complex_sqrt_sq];rfl) (0,1) (by norm_num) t).1
  have he : (A t).1=((A t).1.re : ℂ) := by apply Complex.ext <;> simp [hr]
  change ((scalarStateMass A : ℂ)⁻¹*(A t).1^2).im=0
  rw [he,← Complex.ofReal_inv,← Complex.ofReal_pow,← Complex.ofReal_mul]
  rfl

end NLS.KdV
