import NLS.KdV.HillGradientSecondDerivatives
import NLS.KdV.HillSolutionProductMagri

/-! # The physical weak Magri pairing of the actual independent Hill gradients

The second derivative of the first cotangent is its actual a.e.
derivative proved in HillGradientSecondDerivatives. The weak formula
uses no derivative of q. Integration by parts against periodic first
cotangents gives the usual -d³+4q d+2q_x operator in distribution form.
-/
noncomputable section
open Set Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal
namespace NLS.KdV

def hillWeakGradientMagri (q : Coeff 2) (f df : Curve ℂ) (ddf : ℝ → ℂ) (g dg : Curve ℂ) : ℂ :=
  ∫ x in (0 : ℝ)..1,-ddf x*extend dg x+
    2*hillIntervalPotential q x*(extend f x*extend dg x-extend df x*extend g x)

theorem hillWeakGradientMagri_Dirichlet_eq_product (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (g dg : Curve ℂ) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillDirichletGradientCurve q n hn)
      (hillDirichletGradientSpatialCurve q n hn) (hillDirichletGradientSecond q n hn) g dg =
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        hillSolutionProductMagri (SpectralWeight.one.toCoeff q.val)
          (hillDirichletEnergy q.val q.property.1 q.property.2 n hn) (0,1) (0,1) g dg := by
  rw [hillWeakGradientMagri,hillSolutionProductMagri,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only [scalarHillProductMagriIntegrand,hillDirichletGradientSecond,
    hillDirichletGradientCurve,hillDirichletGradientSpatialCurve,NLS.LinearVolterra.extend,
    ContinuousMap.smul_apply,ContinuousMap.mul_apply,ContinuousMap.pow_apply,ContinuousMap.comp_apply,
    ContinuousMap.fst_apply,ContinuousMap.snd_apply,smul_eq_mul]
  dsimp only [hillDirichletStateCurve,ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk]
  ring

theorem hillWeakGradientMagri_Dirichlet_eq_first (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (g dg : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend g) (extend dg x) x)
    (h0 : g ⟨0,by norm_num⟩ = 0) (h1 : g ⟨1,by norm_num⟩ = 0) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillDirichletGradientCurve q n hn)
      (hillDirichletGradientSpatialCurve q n hn) (hillDirichletGradientSecond q n hn) g dg =
      4*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)*
        (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*extend dg x) := by
  rw [hillWeakGradientMagri_Dirichlet_eq_product,
    hillSolutionProductMagri_eq_first _ _ _ _ g dg hg hdg h0 h1]
  have he : (∫ x in (0 : ℝ)..1,extend (hillDirichletGradientCurve q n hn) x*extend dg x) =
      (scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
        (∫ x in (0 : ℝ)..1,(extend (hillDirichletStateCurve q n hn) x).1*
          (extend (hillDirichletStateCurve q n hn) x).1*extend dg x) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x _
    change ((scalarStateMass (hillDirichletStateCurve q n hn) : ℂ)⁻¹*
      (extend (hillDirichletStateCurve q n hn) x).1^2)*extend dg x = _
    ring
  rw [he]
  dsimp only [hillDirichletStateCurve]
  ring


theorem hillWeakGradientMagri_logNorming_eq_first (q : RealPeriodOneHillPotential)
    (n : ℕ) (hn : 1 ≤ n) (g dg : Curve ℂ)
    (hg : AbsolutelyContinuousOnInterval (extend g) 0 1)
    (hdg : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), HasDerivAt (extend g) (extend dg x) x)
    (h0 : g ⟨0,by norm_num⟩ = 0) (h1 : g ⟨1,by norm_num⟩ = 0) :
    hillWeakGradientMagri (SpectralWeight.one.toCoeff q.val) (hillLogNormingGradientCurve q n hn)
      (hillLogNormingGradientSpatialCurve q n hn) (hillLogNormingGradientSecond q n hn) g dg =
      4*(hillDirichletEnergy q.val q.property.1 q.property.2 n hn : ℂ)*
        (∫ x in (0 : ℝ)..1,extend (hillLogNormingGradientCurve q n hn) x*extend dg x) := by
  let r := SpectralWeight.one.toCoeff q.val
  let mu : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
  let S := hillDirichletStateCurve q n hn
  let C := hillDirichletCosineCurve q n hn
  let alpha := hillLogNormingProjection q n hn
  let B := scalarHillProductMagriIntegrand (hillIntervalPotential r) mu C S g dg
  let D := scalarHillProductMagriIntegrand (hillIntervalPotential r) mu S S g dg
  have hB : IntervalIntegrable B volume 0 1 := intervalIntegrable_scalarHillProductMagriIntegrand _ _ _ _ _ _ (memLp_hillIntervalPotential r)
  have hD : IntervalIntegrable D volume 0 1 := intervalIntegrable_scalarHillProductMagriIntegrand _ _ _ _ _ _ (memLp_hillIntervalPotential r)
  have he : hillWeakGradientMagri r (hillLogNormingGradientCurve q n hn)
      (hillLogNormingGradientSpatialCurve q n hn) (hillLogNormingGradientSecond q n hn) g dg =
        (∫ x in (0 : ℝ)..1,B x)-alpha*(∫ x in (0 : ℝ)..1,D x) := by
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub hB (hD.const_mul alpha)]
    apply intervalIntegral.integral_congr
    intro x _
    dsimp only [hillWeakGradientMagri,B,D,scalarHillProductMagriIntegrand,alpha,r,mu,C,S,
      hillLogNormingGradientSecond,hillLogNormingGradientCurve,hillLogNormingGradientSpatialCurve,
      NLS.LinearVolterra.extend,ContinuousMap.sub_apply,ContinuousMap.add_apply,ContinuousMap.smul_apply,
      ContinuousMap.mul_apply,ContinuousMap.pow_apply,ContinuousMap.comp_apply,
      ContinuousMap.fst,ContinuousMap.snd,ContinuousMap.coe_mk,smul_eq_mul]
    ring
  have hCS : (∫ x in (0 : ℝ)..1,B x) = 4*mu*(∫ x in (0 : ℝ)..1,(extend C x).1*(extend S x).1*extend dg x) :=
    hillSolutionProductMagri_eq_first r mu (1,0) (0,1) g dg hg hdg h0 h1
  have hSS : (∫ x in (0 : ℝ)..1,D x) = 4*mu*(∫ x in (0 : ℝ)..1,(extend S x).1*(extend S x).1*extend dg x) :=
    hillSolutionProductMagri_eq_first r mu (0,1) (0,1) g dg hg hdg h0 h1
  have hi : (∫ x in (0 : ℝ)..1,extend (hillLogNormingGradientCurve q n hn) x*extend dg x) =
      (∫ x in (0 : ℝ)..1,(extend C x).1*(extend S x).1*extend dg x)-
        alpha*(∫ x in (0 : ℝ)..1,(extend S x).1*(extend S x).1*extend dg x) := by
    have hc : Continuous (fun x => (extend C x).1*(extend S x).1*extend dg x) :=
      ((continuous_extend C).fst.mul (continuous_extend S).fst).mul (continuous_extend dg)
    have hd : Continuous (fun x => (extend S x).1*(extend S x).1*extend dg x) :=
      ((continuous_extend S).fst.mul (continuous_extend S).fst).mul (continuous_extend dg)
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hc.intervalIntegrable 0 1) ((hd.intervalIntegrable 0 1).const_mul alpha)]
    apply intervalIntegral.integral_congr
    intro x _
    change ((extend C x).1*(extend S x).1-alpha*(extend S x).1^2)*extend dg x = _
    ring
  rw [he,hCS,hSS,hi]
  ring

end NLS.KdV
