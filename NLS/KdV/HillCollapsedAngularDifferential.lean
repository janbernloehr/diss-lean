import NLS.KdV.HillAbelianCosineDifferential
import NLS.ComplexAnalysis.RealGapZeroPeriod

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable (q : WeightedCoeff SpectralWeight.one.toWeight 2)
    (hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0)
    (hr : IsRealHillPotential (SpectralWeight.one.toCoeff q))

theorem hillAbelianCosineDifferential_of_closed_gap
    (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : 1 ≤ k)
    (hc : hillRealLabels q hq hr (2*k-1) = hillRealLabels q hq hr (2*k)) (θ : ℂ) :
    hillAbelianCosineDifferential q hq hr n hn k θ = if k = n then 1 else 0 := by
  let a : ℂ := hillRealLabels q hq hr (2*k-1)
  let c : ℂ := hillRealGapCenter q hq hr k
  let R := hillRealGapHalfLength q hq hr k+hillRealGapCollar q hq hr k
  let U := hillDeflatedEnergyCanonicalRoot q hq hr k
  let N := hillAbelianSelectedGlobalPsi q hq hr n hn
  let g : ℂ → ℂ := fun E => N E/U E
  have hhalf : hillRealGapHalfLength q hq hr k = 0 := by
    unfold hillRealGapHalfLength
    rw [hc,sub_self,zero_div]
  have hcenter : c = a := by
    dsimp only [c,a,hillRealGapCenter]
    rw [hc]
    push_cast
    ring
  have hR : 0 < R := by
    dsimp only [R]
    rw [hhalf,zero_add]
    exact (hillRealGapContour_geometry q hq hr k hk).2.1
  have hdisc : closedBall c R ⊆ hillGapFilledDomain q hq hr k :=
    hillRealGapContour_closedBall_subset_filledDomain q hq hr k hk
  have hg : AnalyticOnNhd ℂ g (closedBall c R) := by
    intro E hE
    exact (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q hq hr n hn E (mem_univ _)).div
      (analyticOnNhd_hillDeflatedEnergyCanonicalRoot q hq hr k E (hdisc hE))
      (hillDeflatedEnergyCanonicalRoot_ne_zero q hq hr k hk E (hdisc hE))
  have ha : a ∈ ball c R := by rw [hcenter];exact mem_ball_self hR
  have hC := circleIntegral_div_sub_of_differentiable_on_off_countable countable_empty ha
    hg.continuousOn (fun E hE => (hg E (ball_subset_closedBall hE.1)).differentiableAt)
  have hroot (E : ℂ) : endpointRoot a a E = a-E := by
    simp only [endpointRoot,sub_self,zero_pow (by norm_num : 2 ≠ 0),
      normalizedStandardRoot_zeroGap,show (a+a)/2 = a by ring]
  have heq : (fun E => N E/hillEnergyCanonicalRootProduct q hq hr E) =
      (fun E => (-1)*(g E/(E-a))) := by
    funext E
    rw [hillEnergyCanonicalRootProduct_eq_endpoint_mul_deflated q hq hr k hk E,← hc]
    change N E/(endpointRoot a a E*U E) = (-1)*(g E/(E-a))
    rw [hroot,show a-E = -(E-a) by ring]
    dsimp only [g]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_neg]
    ring
  have hp := hillAbelianSelectedGlobalPsi_intrinsic_periods q hq hr n hn k hk
  change (2*(Real.pi : ℂ))⁻¹*(∮ E in C(c,R), N E/hillEnergyCanonicalRootProduct q hq hr E) = _ at hp
  rw [heq,circleIntegral.integral_const_mul,hC] at hp
  have hcoef : (2*(Real.pi : ℂ))⁻¹*((-1)*((2*(Real.pi : ℂ)*I)*g a)) = -I*g a := by
    field_simp
  rw [hcoef] at hp
  change -I*(N (cosineGapPoint c (hillRealGapHalfLength q hq hr k) θ)/U (cosineGapPoint c (hillRealGapHalfLength q hq hr k) θ)) = _
  rw [hhalf,ofReal_zero,cosineGapPoint,zero_mul,add_zero,hcenter]
  exact hp

end NLS.KdV
