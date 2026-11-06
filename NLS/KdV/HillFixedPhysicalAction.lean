import NLS.KdV.HillFixedPhysicalMoments
import NLS.KdV.HillEnergyRootIdentification

noncomputable section
set_option autoImplicit false
open Set Metric Complex
open NLS.ComplexAnalysis
namespace NLS.KdV

/-- The Arnold action formula on any checked real-centered isolating
circle, with the original physical root and original gap normalization. -/
theorem hillFixedContourAction_eq_gapIntegral
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))
    (n : ℕ) (hn : 1 ≤ n) (c R : ℝ) (hR : 0 ≤ R)
    (hband : hillRealLabels q hq hr (2*n-2) < c-R ∧
      c+R < hillRealLabels q hq hr (2*n+1))
    (hgap : segment ℝ (hillRealLabels q hq hr (2*n-1) : ℂ)
      (hillRealLabels q hq hr (2*n) : ℂ) ⊆ ball (c : ℂ) R) :
    (Real.pi : ℂ)⁻¹ * (∮ z in C((c : ℂ),R),
      z * deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillEnergyCanonicalRootProduct q hq hr z) =
      (hillRealGapIntegral q hq hr n 0 : ℂ) := by
  have hs : sphere (c : ℂ) R ⊆ hillL2RealCutDomain q hq hr := by
    intro z hz
    have hre := re_bounds_of_mem_realCenteredClosedBall (sphere_subset_closedBall hz)
    apply mem_hillL2RealCutDomain_of_filled_not_gap q hq hr n hn z
      (Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩)
    exact fun h => sphere_disjoint_ball.le_bot ⟨hz,hgap h⟩
  have hip := circleIntegral_pow_mul_deriv_eq_neg
    (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) (hillL2RealCutDomain q hq hr)
    (analyticOnNhd_hillL2RealCutPrimitive q hq hr) (c : ℂ) R hR hs 0
  have hi : (∮ z in C((c : ℂ),R),
      z * deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
        hillEnergyCanonicalRootProduct q hq hr z) =
      -(∮ z in C((c : ℂ),R), hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q) z) := by
    simpa only [zero_add,pow_one,pow_zero,one_mul,neg_mul,Nat.cast_zero] using
      (calc
        (∮ z in C((c : ℂ),R), z^(0+1) *
            deriv (hillL2Discriminant (SpectralWeight.one.toCoeff q)) z /
              hillEnergyCanonicalRootProduct q hq hr z) =
            ∮ z in C((c : ℂ),R), z^(0+1) *
              deriv (hillL2RealCutPrimitive (SpectralWeight.one.toCoeff q)) z := by
          apply circleIntegral.integral_congr hR
          intro z hz
          dsimp only
          rw [(hasDerivAt_hillL2RealCutPrimitive_energyProduct q hq hr z (hs hz)).deriv]
          exact mul_div_assoc _ _ _
        _ = _ := hip)
  rw [hi,mul_neg]
  simpa only [pow_zero,one_mul,neg_mul] using
    hillFixedContourMoment_eq_gapIntegral q hq hr n hn 0 c R hR hband hgap

end NLS.KdV
