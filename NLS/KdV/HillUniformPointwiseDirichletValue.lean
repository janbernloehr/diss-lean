import NLS.KdV.HillAnalyticQuadraticDirichletValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2) ∈ Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Original Dirichlet terminal evaluation is jointly analytic on a
common geometric domain and preserves any pointwise primitive bound. -/
theorem exists_hillComplexQuadraticDirichletValue_uniform_pointwise_bound (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ U : Set (Coeff 2), U ⊆ ball (0 : Coeff 2) B →
      ∀ k : ℕ, N≤k → ∀ H : ℂ × Coeff 2 → ℂ,
      AnalyticOnNhd ℂ H (ball (hillRealGapCenter 0 h0q h0r k : ℂ)
        (3*(hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4) ×ˢ U) →
      ∀ A : ℝ, (∀ p∈U, ∀ E∈closedBall (hillRealGapCenter 0 h0q h0r k : ℂ)
        ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4), ‖H (E,p)‖≤A) →
      AnalyticOnNhd ℂ (hillComplexQuadraticDirichletValue h0q h0r H k) U ∧
      ∀ p ∈ U, ‖hillComplexQuadraticDirichletValue h0q h0r H k p‖ ≤ ‖hillComplexDirichletGapTerminal h0q h0r k p‖*A := by
  obtain ⟨Nm,hNm,hmu⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Ny,hNy,hterminal⟩ := exists_hillComplexDirichletGapTerminal_analytic_bound h0q h0r B
  refine ⟨max Nm Ny,hNm.trans (le_max_left _ _),?_⟩
  intro U hUB k hk H hH A hbound
  have hkm : Nm ≤ k := (le_max_left _ _).trans hk
  have hky : Ny ≤ k := (le_max_right _ _).trans hk
  have hk1 : 1 ≤ k := hNm.trans hkm
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let μ := hillScaledDirichletRoot h0q h0r (1/16) k
  have hR : 0 < R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB (p : Coeff 2) (hp : p ∈ U) : ‖p‖ ≤ B :=
    (show ‖p‖ < B by simpa only [mem_ball,dist_zero_right] using hUB hp).le
  have hμsmall (p : Coeff 2) (hp : p ∈ U) : μ p ∈ ball c ((1/16)*R) := ((hmu k hkm).2 p (hpB p hp)).1
  have hμB (p : Coeff 2) (hp : p ∈ U) : μ p ∈ ball c (3*R/4) :=
    ball_subset_ball (by linarith : (1/16)*R ≤ 3*R/4) (hμsmall p hp)
  have hμK (p : Coeff 2) (hp : p ∈ U) : μ p ∈ closedBall c (R/4) :=
    closedBall_subset_closedBall (by linarith : (1/16)*R ≤ R/4) (ball_subset_closedBall (hμsmall p hp))
  refine ⟨?_,?_⟩
  · intro p hp
    have hma := (hmu k hkm).1 p (hUB hp)
    have hHa := (hH (μ p,p) ⟨hμB p hp,hp⟩).comp (f := fun a : Coeff 2 => (μ a,a)) (hma.prod analyticAt_id)
    exact (analyticAt_const.mul ((hterminal k hky).1 p (hUB hp))).mul hHa
  · intro p hp
    rw [hillComplexQuadraticDirichletValue,norm_mul,norm_mul,norm_I,one_mul]
    exact mul_le_mul_of_nonneg_left (hbound p hp (μ p) (hμK p hp)) (norm_nonneg _)

end NLS.KdV
