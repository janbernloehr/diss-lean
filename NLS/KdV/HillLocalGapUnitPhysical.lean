import NLS.KdV.HillLocalGapUnit
import NLS.KdV.HillLocalGapPhysicalMatching

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q0 : WeightedCoeff SpectralWeight.one.toWeight 2)
    (h0q : SpectralWeight.one.toCoeff q0 ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff q0))

theorem hillLocalGapUnit_eq_physical_of_geometry
    (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q)) (k : ℕ) (hk : 1 ≤ k)
    (hband : hillRealLabels q hq hr (2*k-2) < hillRealGapCenter q0 h0q h0r k-
        (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) ∧
      hillRealGapCenter q0 h0q h0r k+(hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k) <
        hillRealLabels q hq hr (2*k+1))
    (hgap : segment ℝ (hillRealLabels q hq hr (2*k-1) : ℂ) (hillRealLabels q hq hr (2*k) : ℂ) ⊆
      ball (hillRealGapCenter q0 h0q h0r k : ℂ)
        (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k))
    {z : ℂ} (hz : z ∈ ball (hillRealGapCenter q0 h0q h0r k : ℂ)
      (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k)) :
    hillLocalGapUnit q0 h0q h0r k (z,SpectralWeight.one.toCoeff q) =
      hillDeflatedEnergyCanonicalRoot q hq hr k z ^ 2 := by
  let c : ℂ := hillRealGapCenter q0 h0q h0r k
  let R := hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry q0 h0q h0r k hk).1
    (hillRealGapContour_geometry q0 h0q h0r k hk).2.1
  have hfilled (w : ℂ) (hw : w ∈ closedBall c R) : w ∈ hillGapFilledDomain q hq hr k := by
    have hre := re_bounds_of_mem_realCenteredClosedBall hw
    exact Or.inr ⟨by linarith [hband.1,hre.1],by linarith [hband.2,hre.2]⟩
  obtain ⟨hmid,hsq⟩ := hillLocalGapSymmetricData_eq_physical_of_geometry q0 h0q h0r q hq hr k hk hband hgap
  have hP (w : ℂ) : hillLocalGapPolynomial q0 h0q h0r k (SpectralWeight.one.toCoeff q) w =
      (w-(hillRealLabels q hq hr (2*k-1) : ℂ))*(w-(hillRealLabels q hq hr (2*k) : ℂ)) := by
    rw [hillLocalGapPolynomial,hmid,hsq]
    simp only [hillRealGapCenter,hillRealGapHalfLength,ofReal_div,ofReal_add,ofReal_sub,ofReal_ofNat]
    ring
  have hU : AnalyticOnNhd ℂ (fun w => hillDeflatedEnergyCanonicalRoot q hq hr k w^2) (closedBall c R) :=
    ((analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k).mono hfilled).pow 2
  have hi : (∮ w in C(c,R), hillL2Radicand (SpectralWeight.one.toCoeff q) w /
      hillLocalGapPolynomial q0 h0q h0r k (SpectralWeight.one.toCoeff q) w/(w-z)) =
      ∮ w in C(c,R), hillDeflatedEnergyCanonicalRoot q hq hr k w^2/(w-z) := by
    apply circleIntegral.integral_congr hR.le
    intro w hw
    have ha : w-(hillRealLabels q hq hr (2*k-1) : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw (hgap (left_mem_segment ℝ _ _)))
    have hb : w-(hillRealLabels q hq hr (2*k) : ℂ) ≠ 0 :=
      sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem hw (hgap (right_mem_segment ℝ _ _)))
    dsimp only
    rw [hP,hillL2Radicand_eq_gap_polynomial_mul_deflated_sq q hq hr k hk w
      (hfilled w (sphere_subset_closedBall hw))]
    congr 1
    field_simp
  have hc : (∮ w in C(c,R), hillDeflatedEnergyCanonicalRoot q hq hr k w^2/(w-z)) =
      (2*Real.pi*I)*hillDeflatedEnergyCanonicalRoot q hq hr k z^2 := by
    simpa only [smul_eq_mul,div_eq_mul_inv,mul_comm] using hU.differentiableOn.circleIntegral_sub_inv_smul hz
  change (2*Real.pi*I : ℂ)⁻¹ * (∮ w in C(c,R), hillL2Radicand (SpectralWeight.one.toCoeff q) w /
    hillLocalGapPolynomial q0 h0q h0r k (SpectralWeight.one.toCoeff q) w/(w-z)) = _
  rw [hi,hc]
  have hn : (2*Real.pi*I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  exact inv_mul_cancel_left₀ hn _

theorem exists_hillLocalGapUnit_physical_neighborhood (k : ℕ) (hk : 1 ≤ k) :
    ∃ W : Set RealPeriodOneHillPotential, IsOpen W ∧
      (⟨q0,h0q,h0r⟩ : RealPeriodOneHillPotential) ∈ W ∧
      ∀ p ∈ W, ∀ z ∈ ball (hillRealGapCenter q0 h0q h0r k : ℂ)
        (hillRealGapHalfLength q0 h0q h0r k+hillRealGapCollar q0 h0q h0r k),
        hillLocalGapUnit q0 h0q h0r k (z,SpectralWeight.one.toCoeff p.val) =
          hillDeflatedEnergyCanonicalRoot p.val p.property.1 p.property.2 k z ^ 2 := by
  obtain ⟨W,hW,hqW,hgeo⟩ := exists_hillIntrinsicContour_local_physical_geometry q0 h0q h0r k hk
  refine ⟨W,hW,hqW,?_⟩
  intro p hp z hz
  exact hillLocalGapUnit_eq_physical_of_geometry q0 h0q h0r
    p.val p.property.1 p.property.2 k hk (hgeo p hp).1 (hgeo p hp).2 hz

end NLS.KdV
