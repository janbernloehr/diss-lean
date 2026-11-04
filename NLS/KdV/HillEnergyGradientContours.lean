import NLS.KdV.HillEnergyDiscriminantGradients
import NLS.FunctionalAnalysis.UnitComplexCurvePairing
import NLS.FunctionalAnalysis.CurveSpatialContour

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.LinearVolterra NLS.ZakharovShabat NLS.ComplexAnalysis NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



def hillEnergyGradientContour (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) : Curve ℂ :=
  ∮ z in C(c,r),a z • hillEnergyDiscriminantGradientCurve q z

def hillEnergyGradientSpatialContour (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) : Curve ℂ :=
  ∮ z in C(c,r),a z • hillEnergyDiscriminantGradientSpatialCurve q z

theorem circleIntegrable_hillEnergyGradientContour_integrand
    (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    CircleIntegrable (fun z => a z • hillEnergyDiscriminantGradientCurve q z) c r :=
  (ha.smul ((continuous_hillEnergyDiscriminantGradientCurve_joint.comp
    (continuous_id.prodMk continuous_const)).continuousOn)).circleIntegrable hr

theorem circleIntegrable_hillEnergyGradientSpatialContour_integrand
    (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    CircleIntegrable (fun z => a z • hillEnergyDiscriminantGradientSpatialCurve q z) c r :=
  (ha.smul ((continuous_hillEnergyDiscriminantGradientSpatialCurve_joint.comp
    (continuous_id.prodMk continuous_const)).continuousOn)).circleIntegrable hr

private theorem contour_spatial_data
    (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r)) 0 1 ∧
      ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
        HasDerivAt (NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r))
          (NLS.LinearVolterra.extend (hillEnergyGradientSpatialContour q a c r) x) x := by
  apply circleIntegral_curve_spatial_derivative _ _ c r hr
  · exact ha.smul ((continuous_hillEnergyDiscriminantGradientCurve_joint.comp
      (continuous_id.prodMk continuous_const)).continuousOn)
  · exact ha.smul ((continuous_hillEnergyDiscriminantGradientSpatialCurve_joint.comp
      (continuous_id.prodMk continuous_const)).continuousOn)
  · intro z _
    exact (hillEnergyDiscriminantGradient_H1 q z).1.const_smul (a z)
  · intro z _
    filter_upwards [ae_hasDerivAt_hillEnergyDiscriminantGradientCurve q z] with x hx
    exact hx.const_mul (a z)

theorem ae_hasDerivAt_hillEnergyGradientContour
    (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1),
      HasDerivAt (NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r))
        (NLS.LinearVolterra.extend (hillEnergyGradientSpatialContour q a c r) x) x :=
  (contour_spatial_data q a c r hr ha).2

theorem hillEnergyGradientContour_H1
    (q : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    AbsolutelyContinuousOnInterval (NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r)) 0 1 ∧
      MemLp (NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r)) 2 (volume.restrict (Ioc (0 : ℝ) 1)) ∧
      MemLp (deriv (NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r))) 2 (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have hmem (f : Curve ℂ) : MemLp (NLS.LinearVolterra.extend f) 2 (volume.restrict (Ioc (0 : ℝ) 1)) :=
    (memLp_two_iff_integrable_sq_norm (continuous_extend f).aestronglyMeasurable).mpr
      (((continuous_extend f).norm.pow 2).intervalIntegrable 0 1).1
  refine ⟨(contour_spatial_data q a c r hr ha).1,hmem _,?_⟩
  apply (hmem (hillEnergyGradientSpatialContour q a c r)).ae_eq
  filter_upwards [ae_hasDerivAt_hillEnergyGradientContour q a c r hr ha] with x hx
  exact hx.deriv.symm

theorem unitComplexCurvePairing_hillEnergyGradientContour_eq_zero
    (q : Coeff 2) (a b : ℂ → ℂ) (c d : ℂ) (r s : ℝ) (hr : 0≤r) (hs : 0≤s)
    (ha : ContinuousOn a (sphere c r)) (hb : ContinuousOn b (sphere d s)) :
    unitComplexCurvePairing (hillEnergyGradientContour q a c r) (hillEnergyGradientSpatialContour q b d s)=0 := by
  have hcomm (z w : ℂ) : unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve q z)
      (hillEnergyDiscriminantGradientSpatialCurve q w)=0 :=
    (hillDiscriminantGardnerBracket_eq_curveIntegral q (Complex.sqrt z) (Complex.sqrt w)).symm.trans
      (hillDiscriminantGardnerBracket_eq_zero q (Complex.sqrt z) (Complex.sqrt w))
  rw [hillEnergyGradientContour,hillEnergyGradientSpatialContour,
    bilinear_circleIntegral unitComplexCurvePairing
      (circleIntegrable_hillEnergyGradientContour_integrand q a c r hr ha)
      (circleIntegrable_hillEnergyGradientSpatialContour_integrand q b d s hs hb)]
  simp only [map_smul,smul_apply,hcomm,smul_zero]
  simp only [circleIntegral,smul_zero,intervalIntegral.integral_zero]

/-- Weighted contours of the actual physical energy cotangents have
vanishing genuine Gardner brackets, with the spatial contour proved to be their derivative. -/
theorem hillEnergyGradientContour_GardnerBracket_eq_zero
    (q : Coeff 2) (a b : ℂ → ℂ) (c d : ℂ) (r s : ℝ) (hr : 0≤r) (hs : 0≤s)
    (ha : ContinuousOn a (sphere c r)) (hb : ContinuousOn b (sphere d s)) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r) x*
      deriv (NLS.LinearVolterra.extend (hillEnergyGradientContour q b d s)) x)=0 := by
  calc
    _ = unitComplexCurvePairing (hillEnergyGradientContour q a c r) (hillEnergyGradientSpatialContour q b d s) := by
      apply intervalIntegral.integral_congr_ae_restrict
      rw [uIoc_of_le (by norm_num : (0 : ℝ)≤1)]
      filter_upwards [ae_hasDerivAt_hillEnergyGradientContour q b d s hs hb] with x hx
      change NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r) x*
        deriv (NLS.LinearVolterra.extend (hillEnergyGradientContour q b d s)) x=
        NLS.LinearVolterra.extend (hillEnergyGradientContour q a c r) x*
          NLS.LinearVolterra.extend (hillEnergyGradientSpatialContour q b d s) x
      rw [hx.deriv]
    _ = 0 := unitComplexCurvePairing_hillEnergyGradientContour_eq_zero q a b c d r s hr hs ha hb

end NLS.KdV
