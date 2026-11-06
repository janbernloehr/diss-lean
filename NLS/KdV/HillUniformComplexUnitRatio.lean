import NLS.KdV.HillLocalizedComplexGapPairs
import NLS.KdV.HillFreeGapQuotient
import NLS.ComplexAnalysis.RelativeAnalyticUnitBound
import NLS.ComplexAnalysis.RelativeQuadraticFactorBound

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillFreeGap_bounded_complex_unit_ratio_bound (B : ℝ) :
    ∃ N : ℕ, 1 ≤ N ∧ ∀ p : Coeff 2, ‖p‖ ≤ B → ∀ k : ℕ, N ≤ k →
      ∀ E ∈ ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k),
        ‖hillLocalGapUnit 0 h0q h0r k (E,p)/hillLocalGapUnit 0 h0q h0r k (E,0)-1‖ ≤ 1/4 := by
  obtain ⟨Np,hNp,hpairs⟩ := exists_hillFreeGap_bounded_complex_localized_pairs h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nr,hNr,C,hC,hrelative⟩ := exists_hillScaledFreeGapContour_bounded_complex_relative_bounds h0q h0r 1 (by norm_num) le_rfl B (1/16) (by norm_num)
  refine ⟨max Np Nr,hNp.trans (le_max_left _ _),?_⟩
  intro p hp k hk
  have hkp : Np ≤ k := (le_max_left _ _).trans hk
  have hkr : Nr ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNp.trans hkp
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  obtain ⟨hboundary,a,ha,b,hb,haz,hbz,hm⟩ := hpairs p hp k hkp
  have haB : a ∈ ball c R := ball_subset_ball (by linarith : (1/16)*R ≤ R) ha
  have hbB : b ∈ ball c R := ball_subset_ball (by linarith : (1/16)*R ≤ R) hb
  have haK := ball_subset_closedBall haB
  have hbK := ball_subset_closedBall hbB
  have hab (he : a=b) : deriv (hillL2Radicand p) a=0 := by
    apply deriv_eq_zero_of_two_zero_order (analyticOnNhd_hillL2Radicand p a (mem_univ _)) haz
    simpa [he] using hm a haK
  let Q := twoZeroQuotient (hillL2Radicand p) a b
  let Q₀ := twoZeroQuotient (hillL2Radicand 0) c c
  have hQ := analyticOnNhd_twoZeroQuotient (hillL2Radicand p) (closedBall c R) a b
    ((analyticOnNhd_hillL2Radicand p).mono (subset_univ _)) haK hbK
  obtain ⟨hQ₀,hQ₀n,hunit₀⟩ := hillFreeGap_twoZeroQuotient_unit h0q h0r k hk1
  obtain ⟨hc0,hcd,_,_⟩ := hillFreeGap_two_zero_data h0q h0r k hk1
  have hP₀n (E : ℂ) (hE : E ∈ sphere c R) : (E-c)^2≠0 := by
    apply pow_ne_zero 2
    apply norm_pos_iff.mp
    have he : ‖E-c‖=R := by simpa only [mem_sphere,dist_eq_norm] using hE
    exact he.symm ▸ hR
  have herror (E : ℂ) (hE : E ∈ sphere c R) : ‖hillL2Radicand p E/hillL2Radicand 0 E-1‖ ≤ 1/16 := by
    have hE' : E ∈ sphere c (1*R) := by simpa only [one_mul] using hE
    have hh := hrelative p hp k hkr E hE'
    exact hh.1.trans hh.2.2
  have hpoly (E : ℂ) (hE : E ∈ sphere c R) :
      ‖((E-a)*(E-b))/(E-c)^2-1‖ ≤ 2*(1/16 : ℝ)+(1/16 : ℝ)^2 := by
    apply norm_two_root_factor_div_center_sq_sub_one_le a b c E R (1/16) hR (by norm_num)
    · exact (show ‖a-c‖ < (1/16)*R by simpa only [mem_ball,dist_eq_norm] using ha).le
    · exact (show ‖b-c‖ < (1/16)*R by simpa only [mem_ball,dist_eq_norm] using hb).le
    · simpa only [mem_sphere,dist_eq_norm] using hE
  have hbound := norm_analytic_unit_ratio_sub_one_le_on_disc
    (hillL2Radicand p) (hillL2Radicand 0) (fun E => (E-a)*(E-b)) (fun E => (E-c)^2)
    Q Q₀ c R (1/16) (2*(1/16)+(1/16)^2) hR (by norm_num) hQ hQ₀ hQ₀n hP₀n
    (fun E _ => twoZeroQuotient_factor _ a b haz hbz hab E)
    (fun E _ => by simpa only [pow_two] using twoZeroQuotient_factor (hillL2Radicand 0) c c hc0 hc0 (fun _ => hcd) E)
    herror hpoly
  intro E hE
  rw [hillLocalGapUnit_eq_twoZeroQuotient 0 h0q h0r k hk1 p hboundary haB hbB haz hbz hm hE,hunit₀ E hE]
  exact (hbound E (ball_subset_closedBall hE)).trans (by norm_num)

end NLS.KdV
