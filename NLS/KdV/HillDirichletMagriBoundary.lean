import NLS.KdV.HillWeakGradientMagri

/-! # The exact weak Magri boundary term of a Dirichlet cotangent

A periodic trace cotangent has nonzero endpoint values. Keeping this
term is necessary before reducing its contour-energy weight.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillWeakGradientMagri_Dirichlet_boundary
    (q : RealPeriodOneHillPotential) (n : ℕ) (hn : 1 ≤ n) (g dg : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend g) (extend dg x) x) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillDirichletGradientCurve q n hn)
      (hillDirichletGradientSpatialCurve q n hn) (hillDirichletGradientSecond q n hn) g dg =
        4*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)*
          (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*extend dg x)-
        2*((hillL2DirichletSlope (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn))^2*g ⟨1,by norm_num⟩-
          g ⟨0,by norm_num⟩)/(scalarStateMass (hillDirichletStateCurve q n hn) : ℂ) := by
  let r := SpectralWeight.one.toCoeff q.val
  let mu : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let A := hillDirichletStateCurve q n hn
  have hd : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (fun t => (extend A t).1) (extend A x).2 x ∧
      HasDerivAt (fun t => (extend A t).2) ((hillIntervalPotential r x-mu)*(extend A x).1) x := by
    filter_upwards [ae_hasDerivAt_hillL2FrequencyStateCurve_fst r (Complex.sqrt mu) (0,1),
      ae_hasDerivAt_hillL2FrequencyStateCurve_snd r (Complex.sqrt mu) (0,1)] with x hf hg
    exact ⟨hf,by simpa only [complex_sqrt_sq] using! hg⟩
  have hi := integral_scalarHillProductMagri_eq (hillIntervalPotential r) mu A A g dg
    (memLp_hillIntervalPotential r) (absolutelyContinuousOnInterval_hillStateCurve r (Complex.sqrt mu) (0,1))
    (absolutelyContinuousOnInterval_hillStateCurve r (Complex.sqrt mu) (0,1)) hg hd hd hdg
  have hA0 : extend A 0 = (0,1) := by
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),A,
      hillDirichletStateCurve,hillL2FrequencyStateCurve_zero]
  have hA1 : (extend A 1).1 = 0 := by
    simpa only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num),
      A,hillDirichletStateCurve,hillL2DirichletCharacteristic,hillL2FrequencyDirichlet,hillL2FrequencyStateCurve_apply] using
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 n hn)
  have hs1 : (extend A 1).2 = hillL2DirichletSlope r mu := by
    simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)]
    rfl
  have he : (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*extend dg x) =
      (scalarStateMass A : ℂ)⁻¹*(∫ x in (0 : ℝ)..1,(extend A x).1*(extend A x).1*extend dg x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change ((scalarStateMass A : ℂ)⁻¹*(extend A x).1^2)*extend dg x = _
    ring
  rw [hillWeakGradientMagri_Dirichlet_eq_product]
  change (scalarStateMass A : ℂ)⁻¹*(∫ x in (0 : ℝ)..1,
    scalarHillProductMagriIntegrand (hillIntervalPotential r) mu A A g dg x) = _
  rw [hi,he,hA0,hA1,hs1]
  simp only [NLS.LinearVolterra.extend,projIcc_of_mem _ (show (0 : ℝ) ∈ Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (1 : ℝ) ∈ Icc 0 1 by norm_num)]
  ring

end NLS.KdV
