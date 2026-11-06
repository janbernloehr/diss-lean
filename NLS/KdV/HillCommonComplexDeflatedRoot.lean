import NLS.KdV.HillUniformComplexUnitRatio
import NLS.KdV.HillUniformComplexGapUnit
import NLS.KdV.HillLocalDeflatedComplexRoot
import NLS.ComplexAnalysis.InverseSquareRootBounds

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_normalized_deflated_root (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ k : ℕ, N ≤ k →
      (ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ
        ball (0 : Coeff 2) B ⊆ hillLocalDeflatedRootDomain 0 h0q h0r k) ∧
      AnalyticOnNhd ℂ (hillLocalDeflatedComplexRoot 0 h0q h0r k)
        (ball (hillRealGapCenter 0 h0q h0r k : ℂ) (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k) ×ˢ
          ball (0 : Coeff 2) B) ∧
      ∀ p ∈ ball (0 : Coeff 2) B, ∀ E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillLocalDeflatedComplexRoot 0 h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E-1‖ ≤ 1/4 ∧
        ‖hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillLocalDeflatedComplexRoot 0 h0q h0r k (E,p)-1‖ ≤ 1/2 := by
  obtain ⟨Nr,hNr,hratio⟩ := exists_hillFreeGap_bounded_complex_unit_ratio_bound h0q h0r B
  obtain ⟨Nu,hNu,hunit⟩ := exists_hillFreeGap_bounded_complex_analytic_unit h0q h0r B
  refine ⟨max Nr Nu,hNr.trans (le_max_left _ _),?_⟩
  intro k hk
  have hkr : Nr ≤ k := (le_max_left _ _).trans hk
  have hku : Nu ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNr.trans hkr
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hpB (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) : ‖p‖ ≤ B :=
    (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hp).le
  have hratio' (p : Coeff 2) (hp : p ∈ ball (0 : Coeff 2) B) (E : ℂ) (hE : E ∈ ball c R) :
      ‖hillLocalDeflatedRootRatio 0 h0q h0r k (E,p)-1‖ ≤ 1/4 := by
    have hh := hratio p (hpB p hp) k hkr E hE
    have he := hillLocalGapUnit_at_base 0 h0q h0r k hk1 E hE
    rw [map_zero] at he
    simpa only [hillLocalDeflatedRootRatio,he] using hh
  have hdom : ball c R ×ˢ ball (0 : Coeff 2) B ⊆ hillLocalDeflatedRootDomain 0 h0q h0r k := by
    intro t ht
    refine ⟨⟨(hunit k hku).1 t ht,ht.1,mem_univ _⟩,?_⟩
    exact mem_slitPlane_of_norm_sub_one_le_half _ ((hratio' t.2 ht.2 t.1 ht.1).trans (by norm_num))
  refine ⟨hdom,(analyticOnNhd_hillLocalDeflatedComplexRoot 0 h0q h0r k hk1).mono hdom,?_⟩
  intro p hp E hE
  have hfree := hillDeflatedEnergyCanonicalRoot_ne_zero 0 h0q h0r k hk1 E
    (hillRealGapContour_closedBall_subset_filledDomain 0 h0q h0r k hk1 (ball_subset_closedBall hE))
  have hsmall := hratio' p hp E hE
  have hrat : hillLocalDeflatedComplexRoot 0 h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E =
      sqrt (hillLocalDeflatedRootRatio 0 h0q h0r k (E,p)) := by
    rw [hillLocalDeflatedComplexRoot,mul_div_cancel_left₀ _ hfree]
  constructor
  · rw [hrat]
    exact (norm_sqrt_sub_one_le _).trans hsmall
  · rw [show hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E/hillLocalDeflatedComplexRoot 0 h0q h0r k (E,p) =
      (hillLocalDeflatedComplexRoot 0 h0q h0r k (E,p)/hillDeflatedEnergyCanonicalRoot 0 h0q h0r k E)⁻¹ by rw [inv_div],hrat]
    exact (norm_inv_sqrt_sub_one_le _ (hsmall.trans (by norm_num))).trans (by linarith)

end NLS.KdV
