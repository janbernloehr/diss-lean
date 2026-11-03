import NLS.KdV.HillDirichletGradients
import NLS.KdV.ClassicalL2PrimitiveAgreement
import NLS.Fourier.ContinuousConstants
import NLS.ComplexAnalysis.MixedSpectralSourceDerivative

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open MeasureTheory NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal

namespace NLS.KdV

theorem classicalHillFlow_constant_shift (q : Curve ℂ) (a c : ℂ) (v : ℂ × ℂ) :
    classicalHillFlow (q+ContinuousMap.const _ c) (a+c) v=classicalHillFlow q a v := by
  have he : classicalHillCoefficientCurve (q+ContinuousMap.const _ c) (a+c)=
      classicalHillCoefficientCurve q a := by
    apply ContinuousMap.ext
    intro t
    apply ContinuousLinearMap.ext
    intro w
    change (w.2,((q t+c)-(a+c))*w.1)=(w.2,(q t-a)*w.1)
    congr 1
    ring
  simp only [classicalHillFlow,he]

theorem hillL2DirichletSlope_constant_shift (q : Coeff 2) (a c : ℂ) :
    hillL2DirichletSlope (q+lp.single 2 0 c) (a+c)=hillL2DirichletSlope q a := by
  have hc (e : ℂ) : Continuous (fun p : Coeff 2 => hillL2DirichletSlope p e) := by
    have hj : Continuous (fun p : ℂ × Coeff 2 => hillL2DirichletSlope p.2 p.1) :=
      continuous_iff_continuousAt.mpr (fun p =>
        (analyticOnNhd_hillL2DirichletSlope_joint p (mem_univ _)).continuousAt)
    convert! hj.comp (continuous_const.prodMk continuous_id) using 1
  have hfinite (f : ℤ →₀ ℂ) :
      hillL2DirichletSlope (Coeff.ofFinsupp (p := 2) f+lp.single 2 0 c) (a+c)=
        hillL2DirichletSlope (Coeff.ofFinsupp (p := 2) f) a := by
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
    rw [← hR,← hQ,hillL2DirichletSlope_eq_classical,hillL2DirichletSlope_eq_classical]
    have he : hillUnitPotentialCurve R=hillUnitPotentialCurve Q+ContinuousMap.const _ c := by
      ext t
      rfl
    rw [he,classicalHillFlow_constant_shift]
  have heq := (Coeff.denseRange_ofFinsupp (p := 2) (by simp)).equalizer
    ((hc (a+c)).comp (continuous_id.add continuous_const)) (hc a) (funext hfinite)
  exact congrFun heq q

theorem hillL2DirichletSlope_energy_deriv_eq_constant_direction
    (q : Coeff 2) (a : ℂ) :
    deriv (hillL2DirichletSlope q) a=
      -((fderiv ℂ (fun p : Coeff 2 => hillL2DirichletSlope p a) q) (lp.single 2 0 1)) := by
  let e : Coeff 2 := lp.single 2 0 1
  let F : ℂ × Coeff 2 → ℂ := fun p => hillL2DirichletSlope p.2 p.1
  have hF : DifferentiableAt ℂ F (a,q) :=
    (analyticOnNhd_hillL2DirichletSlope_joint (a,q) (mem_univ _)).differentiableAt
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
  have heq : (fun c : ℂ => F (a+c,q+c • e))=(fun _ : ℂ => hillL2DirichletSlope q a) := by
    funext c
    change hillL2DirichletSlope (q+c • e) (a+c)=hillL2DirichletSlope q a
    rw [← hsingle,hillL2DirichletSlope_constant_shift]
  change HasDerivAt (fun c : ℂ => F (a+c,q+c • e)) ((fderiv ℂ F (a,q)) (1,e)) 0 at hc
  rw [heq] at hc
  have hz : (fderiv ℂ F (a,q)) (1,e)=0 := hc.unique (hasDerivAt_const 0 _)
  rw [deriv_spectral_section_eq_fderiv F a q hF,fderiv_source_section_eq_joint F a q hF]
  change (fderiv ℂ F (a,q)) (1,0)= -(fderiv ℂ F (a,q)) (0,e)
  have hp : ((1 : ℂ),e)=((1 : ℂ),(0 : Coeff 2))+((0 : ℂ),e) := by ext <;> simp
  rw [hp,map_add] at hz
  linear_combination hz

theorem hillPhysicalDirection_one_lower_ae :
    ∀ᵐ x ∂MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1),
      (hillPhysicalDirection (lp.single 2 0 1)).ofLp.2 x= -1 := by
  let U (q : Coeff 2) := physicalRestrictionL2 (hillFirstOrderPotential q)
  have hU (c : ℂ) : intervalL2Representative (U (lp.single 2 0 c))
      =ᵐ[MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)] (fun _ => ((-1 : ℂ),-c)) := by
    let Q := ContinuousMap.const (AddCircle (2 : ℝ)) c
    have hc : SpectralWeight.one.toCoeff (hillContinuousCoefficients Q)=(lp.single 2 0 c : Coeff 2) := by
      rw [toCoeff_hillContinuousCoefficients,Fourier.continuousFourierCLM_const]
    have ht := hillFirstOrder_continuous_compatibility Q
    rw [hc] at ht
    filter_upwards [physicalRestrictionL2_representative (hillFirstOrderPotential (lp.single 2 0 c)),ht] with x hx hy
    rw [hx,hy]
    rfl
  let e : Coeff 2 := lp.single 2 0 1
  have he : U e=hillPhysicalDirection e+U 0 := by
    change physicalRestrictionL2CLM (hillFirstOrderPotential e)=
      physicalRestrictionL2CLM (hillFirstOrderDirection e)+physicalRestrictionL2CLM (hillFirstOrderPotential 0)
    rw [← map_add]
    congr 1
    simp [hillFirstOrderPotential,hillFirstOrderDirection_apply]
  have hr := intervalL2Representative_add (hillPhysicalDirection e) (U 0)
  rw [← he] at hr
  have h0 : intervalL2Representative (U 0)=ᵐ[MeasureTheory.volume.restrict (Ioc (0 : ℝ) 1)]
      (fun _ => ((-1 : ℂ),0)) := by simpa using hU 0
  filter_upwards [hr,hU 1,h0] with x hx h1 h0
  have hf := congrArg Prod.snd hx
  change (intervalL2Representative (U e) x).2=
    (hillPhysicalDirection e).ofLp.2 x+(intervalL2Representative (U 0) x).2 at hf
  change intervalL2Representative (U e) x=(-1,-1) at h1
  rw [h1,h0] at hf
  dsimp only [Prod.snd] at hf
  change (hillPhysicalDirection e).ofLp.2 x= -1
  linear_combination -hf

end NLS.KdV
