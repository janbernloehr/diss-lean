import NLS.KdV.HillEnergyGradientContours

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open NLS.ComplexAnalysis NLS.ZakharovShabat NLS.LinearVolterra NLS.FunctionalAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



private theorem contour_endpoints (F : ℂ → Curve ℂ) (c : ℂ) (r : ℝ) (hr : 0≤r)
    (hF : CircleIntegrable F c r)
    (he : ∀ z∈sphere c r, F z ⟨0,by norm_num⟩=F z ⟨1,by norm_num⟩) :
    (∮ z in C(c,r),F z) ⟨0,by norm_num⟩=(∮ z in C(c,r),F z) ⟨1,by norm_num⟩ := by
  change (ContinuousMap.evalCLM ℂ (⟨0,by norm_num⟩ : Icc (0 : ℝ) 1)) (∮ z in C(c,r),F z)=
    (ContinuousMap.evalCLM ℂ (⟨1,by norm_num⟩ : Icc (0 : ℝ) 1)) (∮ z in C(c,r),F z)
  rw [map_circleIntegral _ hF,map_circleIntegral _ hF]
  apply circleIntegral.integral_congr hr
  intro z hz
  exact he z hz

theorem hillEnergyGradientContours_closed (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    (hillEnergyGradientContour p a c r) ⟨0,by norm_num⟩=
      (hillEnergyGradientContour p a c r) ⟨1,by norm_num⟩ ∧
    (hillEnergyGradientSpatialContour p a c r) ⟨0,by norm_num⟩=
      (hillEnergyGradientSpatialContour p a c r) ⟨1,by norm_num⟩ := by
  constructor
  · apply contour_endpoints _ c r hr (circleIntegrable_hillEnergyGradientContour_integrand p a c r hr ha)
    intro z _
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    dsimp only [hillEnergyDiscriminantGradientCurve]
    rw [(hillDiscriminantGradientCurve_endpoints p (Complex.sqrt z)).1,
      (hillDiscriminantGradientCurve_endpoints p (Complex.sqrt z)).2]
  · apply contour_endpoints _ c r hr (circleIntegrable_hillEnergyGradientSpatialContour_integrand p a c r hr ha)
    intro z _
    simp only [ContinuousMap.smul_apply,smul_eq_mul]
    dsimp only [hillEnergyDiscriminantGradientSpatialCurve]
    rw [(hillDiscriminantGradientSpatialCurve_endpoints p (Complex.sqrt z)).1,
      (hillDiscriminantGradientSpatialCurve_endpoints p (Complex.sqrt z)).2]

/-- Every actual energy discriminant commutes with a weighted spatial
gradient contour, as a bounded physical bilinear pairing. -/
theorem unitComplexCurvePairing_energy_spatialContour_eq_zero
    (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) (energy : ℂ) :
    unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve p energy)
      (hillEnergyGradientSpatialContour p a c r)=0 := by
  have hcomm (z : ℂ) : unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve p energy)
      (hillEnergyDiscriminantGradientSpatialCurve p z)=0 :=
    (hillDiscriminantGardnerBracket_eq_curveIntegral p (Complex.sqrt energy) (Complex.sqrt z)).symm.trans
      (hillDiscriminantGardnerBracket_eq_zero p (Complex.sqrt energy) (Complex.sqrt z))
  rw [hillEnergyGradientSpatialContour,
    map_circleIntegral (unitComplexCurvePairing (hillEnergyDiscriminantGradientCurve p energy))
      (circleIntegrable_hillEnergyGradientSpatialContour_integrand p a c r hr ha)]
  simp only [map_smul,hcomm,smul_zero,circleIntegral,intervalIntegral.integral_zero]

theorem hillEnergyGradientSpatialContour_integral_eq_zero
    (p : Coeff 2) (a : ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hr : 0≤r) (ha : ContinuousOn a (sphere c r)) :
    (∫ x in (0 : ℝ)..1,NLS.LinearVolterra.extend (hillEnergyGradientSpatialContour p a c r) x)=0 := by
  have hd := ae_hasDerivAt_hillEnergyGradientContour p a c r hr ha
  rw [restrict_Ioc_eq_restrict_Icc] at hd
  have he := (ae_restrict_iff' measurableSet_Icc).mp hd
  have hh := integral_eq_sub_of_ac_of_ae_hasDerivAt (hillEnergyGradientContour_H1 p a c r hr ha).1
    ((continuous_extend (hillEnergyGradientSpatialContour p a c r)).intervalIntegrable 0 1)
    (by simpa only [uIcc_of_le (by norm_num : (0 : ℝ)≤1)] using he)
  rw [hh]
  dsimp only [NLS.LinearVolterra.extend]
  rw [projIcc_of_mem _ (show (1 : ℝ)∈Icc 0 1 by norm_num),
    projIcc_of_mem _ (show (0 : ℝ)∈Icc 0 1 by norm_num),
    (hillEnergyGradientContours_closed p a c r hr ha).1,sub_self]

end NLS.KdV
