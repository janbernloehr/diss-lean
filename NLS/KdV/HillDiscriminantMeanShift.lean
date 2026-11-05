import NLS.KdV.HillDirichletSlopeShift
import NLS.KdV.HillEnergyDiscriminantGradients

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.FunctionalAnalysis NLS.LinearVolterra
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



theorem hillL2Discriminant_constant_shift (q : Coeff 2) (a c : ℂ) :
    hillL2Discriminant (q+lp.single 2 0 c) (a+c)=hillL2Discriminant q a := by
  have hc (e : ℂ) : Continuous (fun p : Coeff 2 => hillL2Discriminant p e) := by
    have hj : Continuous (fun p : ℂ × Coeff 2 => hillL2Discriminant p.2 p.1) :=
      continuous_iff_continuousAt.mpr (fun p =>
        (analyticOnNhd_hillL2Discriminant_joint p (mem_univ _)).continuousAt)
    convert! hj.comp (continuous_const.prodMk continuous_id) using 1
  have hfinite (f : ℤ →₀ ℂ) :
      hillL2Discriminant (Coeff.ofFinsupp (p := 2) f+lp.single 2 0 c) (a+c)=
        hillL2Discriminant (Coeff.ofFinsupp (p := 2) f) a := by
    let Q := Fourier.continuousSynthesis (Coeff.ofFinsupp (p := 1) f)
    let R := Q+ContinuousMap.const (AddCircle (2 : ℝ)) c
    have hQ : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=Coeff.ofFinsupp (p := 2) f := by
      ext k
      rw [SpectralWeight.toCoeff_apply,hillContinuousCoefficients_apply]
      exact Fourier.fourierCoeff_continuousSynthesis _ k
    have hR : SpectralWeight.one.toCoeff (hillContinuousCoefficients R)=Coeff.ofFinsupp (p := 2) f+lp.single 2 0 c := by
      rw [toCoeff_hillContinuousCoefficients]
      dsimp only [R]
      rw [map_add,Fourier.continuousFourierCLM_const,← toCoeff_hillContinuousCoefficients,hQ]
    rw [← hR,← hQ,hillL2Discriminant_eq_classical,hillL2Discriminant_eq_classical]
    have he : hillUnitPotentialCurve R=hillUnitPotentialCurve Q+ContinuousMap.const _ c := by
      ext t
      rfl
    rw [he,←classicalHillFlow_trace,←classicalHillFlow_trace,
      classicalHillFlow_constant_shift,classicalHillFlow_constant_shift]
  have heq := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    ((hc (a+c)).comp (continuous_id.add continuous_const)) (hc a) (funext hfinite)
  exact congrFun heq q

theorem hillL2Discriminant_energy_deriv_eq_constant_direction
    (q : Coeff 2) (a : ℂ) :
    deriv (hillL2Discriminant q) a=
      -((fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p a) q) (lp.single 2 0 1)) := by
  let e : Coeff 2 := lp.single 2 0 1
  let F : ℂ × Coeff 2 → ℂ := fun p => hillL2Discriminant p.2 p.1
  have hF : DifferentiableAt ℂ F (a,q) :=
    (analyticOnNhd_hillL2Discriminant_joint (a,q) (mem_univ _)).differentiableAt
  have hline : HasDerivAt (fun c : ℂ => (a+c,q+c • e)) (1,e) 0 := by
    convert! ((hasDerivAt_id (0 : ℂ)).const_add a).prodMk
      (((hasDerivAt_id (0 : ℂ)).smul_const e).const_add q) using 1
    simp
  have hF' : DifferentiableAt ℂ F (a+(0 : ℂ),q+(0 : ℂ) • e) := by simpa using hF
  have hc := hF'.hasFDerivAt.comp_hasDerivAt 0 hline
  simp only [add_zero,zero_smul] at hc
  have hsingle (c : ℂ) : (lp.single 2 0 c : Coeff 2)=c • e := by
    ext k
    by_cases hk : k=0 <;> simp [e,lp.single_apply,hk]
  have heq : (fun c : ℂ => F (a+c,q+c • e))=(fun _ : ℂ => hillL2Discriminant q a) := by
    funext c
    change hillL2Discriminant (q+c • e) (a+c)=hillL2Discriminant q a
    rw [← hsingle,hillL2Discriminant_constant_shift]
  change HasDerivAt (fun c : ℂ => F (a+c,q+c • e)) ((fderiv ℂ F (a,q)) (1,e)) 0 at hc
  rw [heq] at hc
  have hz : (fderiv ℂ F (a,q)) (1,e)=0 := hc.unique (hasDerivAt_const 0 _)
  rw [deriv_spectral_section_eq_fderiv F a q hF,fderiv_source_section_eq_joint F a q hF]
  change (fderiv ℂ F (a,q)) (1,0)= -(fderiv ℂ F (a,q)) (0,e)
  have hp : ((1 : ℂ),e)=((1 : ℂ),(0 : Coeff 2))+((0 : ℂ),e) := by ext <;> simp
  rw [hp,map_add] at hz
  linear_combination hz


/-- The physical discriminant cotangent has mass equal to minus the energy derivative. -/
theorem hillEnergyDiscriminantGradient_integral_eq_neg_deriv (p : Coeff 2) (E : ℂ) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillEnergyDiscriminantGradientCurve p E) x)=
      -deriv (hillL2Discriminant p) E := by
  rw [hillL2Discriminant_energy_deriv_eq_constant_direction,neg_neg,
    hillEnergyDiscriminantGradient_represents_potential,hillPhysicalDirectionPairing_apply]
  apply intervalIntegral.integral_congr_ae_restrict
  rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
  filter_upwards [hillPhysicalDirection_one_lower_ae] with x hx
  rw [hx,neg_neg,one_mul]

end NLS.KdV
