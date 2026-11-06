import NLS.KdV.HillUniformComplexGapData
import NLS.KdV.HillLocalGapUnit
import NLS.KdV.HillLocalGapUnitPhysical

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_analytic_unit (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      AnalyticOnNhd ℂ (hillLocalGapUnit 0 h0q h0r k)
        (ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ ball (0 : Coeff 2) B) ∧
      ∀ p ∈ ball (0 : Coeff 2) B,
        ∀ z ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillL2Radicand p z = hillLocalGapPolynomial 0 h0q h0r k p z*hillLocalGapUnit 0 h0q h0r k (z,p) ∧
          hillLocalGapUnit 0 h0q h0r k (z,p) ≠ 0 := by
  obtain ⟨N,hN,hdata⟩ := exists_hillFreeGap_bounded_complex_analytic_symmetric_data h0q h0r B
  refine ⟨N,hN,?_⟩
  intro k hk
  have hk1 := hN.trans hk
  obtain ⟨hM,hS,hpair⟩ := hdata k hk
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hP : AnalyticOnNhd ℂ (fun t : ℂ × Coeff 2 => hillLocalGapPolynomial 0 h0q h0r k t.2 t.1)
      (sphere c R ×ˢ ball (0 : Coeff 2) B) := by
    intro t ht
    exact ((analyticAt_fst.sub ((hM t.2 ht.2).comp analyticAt_snd)).pow 2).sub
      (((hS t.2 ht.2).comp analyticAt_snd).div_const)
  have hPn (t : ℂ × Coeff 2) (ht : t ∈ sphere c R ×ˢ ball (0 : Coeff 2) B) :
      hillLocalGapPolynomial 0 h0q h0r k t.2 t.1 ≠ 0 := by
    obtain ⟨hb,a,ha,b,hb',_,_,hm,_,_⟩ := hpair t.2 ht.2
    rw [hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk1 t.2 hb ha hb' hm]
    exact mul_ne_zero (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem ht.1 ha))
      (sub_ne_zero.mpr (sphere_disjoint_ball.ne_of_mem ht.1 hb'))
  have hF : AnalyticOnNhd ℂ
      (fun t : ℂ × Coeff 2 => hillL2Radicand t.2 t.1/hillLocalGapPolynomial 0 h0q h0r k t.2 t.1)
      (sphere c R ×ˢ ball (0 : Coeff 2) B) := by
    intro t ht
    exact (analyticOnNhd_hillL2Radicand_joint t (mem_univ _)).div (hP t ht) (hPn t ht)
  have hC := analyticOnNhd_parametricCircleCauchyTransform _ c R hR.le (ball (0 : Coeff 2) B) isOpen_ball hF
  refine ⟨hC.mono (fun t ht => ⟨fun he => (ne_of_lt ht.1) he,ht.2⟩),?_⟩
  intro p hp z hz
  obtain ⟨hb,a,ha,b,hb',haz,hbz,hm,_,_⟩ := hpair p hp
  have hPpoly := hillLocalGapPolynomial_eq_of_pair 0 h0q h0r k hk1 p hb ha hb' hm
  have hunit : hillLocalGapUnit 0 h0q h0r k (z,p) =
      circleCauchyTransform (fun w => hillL2Radicand p w/((w-a)*(w-b))) c R z := by
    change circleCauchyTransform (fun w => hillL2Radicand p w/hillLocalGapPolynomial 0 h0q h0r k p w) c R z = _
    congr 1
    funext w
    rw [hPpoly]
  rw [hunit,hPpoly]
  exact circleCauchyTransform_two_zero_unit _ hR
    ((analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) hb ha hb' haz hbz hm hz

theorem exists_hillFreeGap_bounded_real_unit_matching (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ q : WeightedCoeff SpectralWeight.one.toWeight 2,
      ∀ hq : SpectralWeight.one.toCoeff q ∈ Coeff.paritySubspace 0,
      ∀ hr : IsRealHillPotential (SpectralWeight.one.toCoeff q), ‖SpectralWeight.one.toCoeff q‖ ≤ B →
        ∀ k : ℕ, N ≤ k → ∀ z ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
          (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
          hillLocalGapUnit 0 h0q h0r k (z,SpectralWeight.one.toCoeff q) = hillDeflatedEnergyCanonicalRoot q hq hr k z^2 := by
  obtain ⟨N,hN,D,hD,hcontrol⟩ := exists_hillComplexTailPeriodControl h0q h0r B
  refine ⟨N,hN,?_⟩
  intro q hq hr hp k hk z hz
  exact hillLocalGapUnit_eq_physical_of_geometry 0 h0q h0r q hq hr k (hN.trans hk)
    (hillHighFreeContour_physical_band_bounds_of_control h0q h0r N hN B D hcontrol q hq hr hp k hk)
    (hillRealGap_mem_high_free_contour_ball_of_control h0q h0r N hN B D hcontrol q hq hr hp k hk) hz

end NLS.KdV
