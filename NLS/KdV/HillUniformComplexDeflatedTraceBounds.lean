import NLS.KdV.HillUniformComplexTraceBounds
import NLS.KdV.HillUniformDeflatedInverseBounds
import NLS.KdV.HillCommonComplexDeflatedTrace

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis
open scoped ENNReal Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

theorem exists_hillComplexDeflatedTraceNumerator_uniform_half_disc_bound :
    ∃ C : ℝ, 0<C ∧ ∀ B : ℝ, ∃ N : ℕ, 1≤N ∧ ∀ p : Coeff 2, ‖p‖≤B →
      ∀ k : ℕ, N≤k → ∀ E ∈ closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/2),
        ‖hillComplexDeflatedTraceNumerator h0q h0r k (E,p)‖ ≤ C := by
  obtain ⟨D,hD,htrace⟩ := exists_hillL2Discriminant_uniform_complex_free_disc_bound h0q h0r
  obtain ⟨A,hA,hinverse⟩ := exists_hillFilledFreeGapRoot_uniform_inverse_bound h0q h0r
  refine ⟨2*D*A,by positivity,?_⟩
  intro B
  obtain ⟨Nt,hNt,ht⟩ := htrace B
  obtain ⟨Nr,hNr,hr⟩ := hinverse B
  refine ⟨Nt+Nr,hNt.trans (by omega),?_⟩
  intro p hp k hk E hE
  have hkt : Nt≤k := by omega
  have hkr : Nr≤k := by omega
  have hk1 := hNt.trans hkt
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hE' : E∈closedBall c R := closedBall_subset_closedBall (by linarith : R/2≤R) hE
  have hder : ‖deriv (hillL2Discriminant p) E‖≤D/(R-R/2) :=
    norm_deriv_le_of_closedDisc_bound
      (fun z => (analyticOnNhd_hillL2Discriminant p z (mem_univ _)).differentiableAt)
      c (by linarith : R/2<R) D
      (fun z hz => ht p hp k hkt z (by simpa only [mem_closedBall,dist_eq_norm] using hz))
      (by simpa only [mem_closedBall,dist_eq_norm] using hE)
  have hmargin : 0<R-R/2 := by linarith
  rw [hillComplexDeflatedTraceNumerator,div_eq_mul_inv,norm_mul]
  exact (mul_le_mul hder (hr p hp k hkr E hE') (norm_nonneg _) (by positivity : 0≤D/(R-R/2))).trans_eq
    (by field_simp;ring)

end NLS.KdV
