import NLS.KdV.HillPhysicalActionGradients
import NLS.KdV.HillIntrinsicPeriodReality

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.FunctionalAnalysis
namespace NLS.KdV

/-- The ORIGINAL action differential is exactly minus twice the intrinsic
period of the ACTUAL entire discriminant variation, at EVERY positive gap. -/
theorem hillOriginalAction_variation_eq_intrinsic_period
    (q : RealPeriodOneHillPotential) (n : ℕ+) (h : Coeff 2) :
    (fderiv ℂ (hillRealSourceMoment q.val q.property.1 q.property.2 n 0)
        (SpectralWeight.one.toCoeff q.val)) h =
      -2 * hillIntrinsicGapPeriod q.val q.property.1 q.property.2 n
        (fun E => (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
          (SpectralWeight.one.toCoeff q.val)) h) := by
  let p := SpectralWeight.one.toCoeff q.val
  let c : ℂ := hillRealGapCenter q.val q.property.1 q.property.2 n
  let R := hillRealGapHalfLength q.val q.property.1 q.property.2 n +
    hillRealGapCollar q.val q.property.1 q.property.2 n
  have hR : 0 ≤ R := add_nonneg
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 n n.pos).1
    (hillRealGapContour_geometry q.val q.property.1 q.property.2 n n.pos).2.1.le
  rw [hillRealSourceMoment_gradient q.val q.property.1 q.property.2 n n.pos 0,
    hillPhysicalMomentGradient,hillEnergyGradientContour,
    map_circleIntegral (hillPhysicalDirectionPairing h)
      (circleIntegrable_hillEnergyGradientContour_integrand p
        (hillPhysicalMomentGradientWeight p 0) c R hR
        (continuousOn_hillPhysicalMomentGradientWeight q.val q.property.1 q.property.2 n n.pos 0))]
  simp only [map_smul,smul_eq_mul]
  simp_rw [←hillEnergyDiscriminantGradient_represents_potential p h]
  have hi : (∮ E in C(c,R), hillPhysicalMomentGradientWeight p 0 E *
      (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E) p) h) =
      -(Real.pi:ℂ)⁻¹ * ∮ E in C(c,R),
        (fderiv ℂ (fun a : Coeff 2 => hillL2Discriminant a E) p) h /
          hillEnergyCanonicalRootProduct q.val q.property.1 q.property.2 E := by
    rw [←circleIntegral.integral_const_mul]
    apply circleIntegral.integral_congr hR
    intro E hE
    dsimp only [hillPhysicalMomentGradientWeight]
    rw [←hillEnergyCanonicalRootProduct_eq_realCutRoot q.val q.property.1 q.property.2
      (hillRealGapContour_sphere_subset q.val q.property.1 q.property.2 n n.pos hE)]
    simp only [pow_zero]
    ring
  rw [hi]
  unfold hillIntrinsicGapPeriod
  have hpi : (Real.pi:ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring

theorem hillTraceVariation_periods_zero_of_action_kernel
    (q : RealPeriodOneHillPotential) (h : Coeff 2)
    (hkernel : ∀ n : ℕ+, (fderiv ℂ (hillRealSourceMoment q.val q.property.1 q.property.2 n 0)
      (SpectralWeight.one.toCoeff q.val)) h = 0) :
    ∀ k : ℕ, 1 ≤ k → hillIntrinsicGapPeriod q.val q.property.1 q.property.2 k
      (fun E => (fderiv ℂ (fun p : Coeff 2 => hillL2Discriminant p E)
        (SpectralWeight.one.toCoeff q.val)) h) = 0 := by
  intro k hk
  have he := hillOriginalAction_variation_eq_intrinsic_period q ⟨k,hk⟩ h
  rw [hkernel ⟨k,hk⟩] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (by norm_num)

end NLS.KdV
