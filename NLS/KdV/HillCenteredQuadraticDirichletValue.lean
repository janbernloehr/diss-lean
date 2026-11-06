import NLS.KdV.HillUniformCenteredMeanFreePrimitives
import NLS.KdV.HillUniformPointwiseDirichletValue

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open NLS.ComplexAnalysis NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate Classical

namespace NLS.KdV



variable
    (h0q : SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)∈Coeff.paritySubspace 0)
    (h0r : IsRealHillPotential (SpectralWeight.one.toCoeff (0 : WeightedCoeff SpectralWeight.one.toWeight 2)))

/-- Original Dirichlet sheet times the primitive evaluated in the
original complex midpoint coordinate. -/
def hillCenteredQuadraticDirichletValue (Q : ℂ × Coeff 2 → ℂ) (k : ℕ) (p : Coeff 2) : ℂ :=
  I*hillComplexDirichletGapTerminal h0q h0r k p*
    Q (hillScaledDirichletRoot h0q h0r (1/16) k p-hillLocalGapMidpoint 0 h0q h0r k p,p)

/-- The original centered Dirichlet evaluation preserves a common
primitive bound on a fixed fraction of the actual gap-disc radius. -/
theorem exists_hillCenteredQuadraticDirichletValue_uniform_pointwise_bound (B : ℝ) :
    ∃ N : ℕ, 1≤N ∧ ∀ U : Set (Coeff 2), U⊆ball (0 : Coeff 2) B →
      ∀ k : ℕ, N≤k → ∀ Q : ℂ × Coeff 2 → ℂ,
      AnalyticOnNhd ℂ Q (ball (0:ℂ)
        ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/4) ×ˢ U) →
      ∀ A : ℝ, (∀ p∈U, ∀ w∈closedBall (0:ℂ)
        ((hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k)/8), ‖Q (w,p)‖≤A) →
      AnalyticOnNhd ℂ (hillCenteredQuadraticDirichletValue h0q h0r Q k) U ∧
      ∀ p∈U, ‖hillCenteredQuadraticDirichletValue h0q h0r Q k p‖≤‖hillComplexDirichletGapTerminal h0q h0r k p‖*A := by
  obtain ⟨Nm,hNm,hmu⟩ := exists_hillScaledDirichletRoot_bounded_complex_analytic_chart h0q h0r (1/16) (by norm_num) (by norm_num) B
  obtain ⟨Nc,hNc,hcenter⟩ := exists_hillLocalGap_bounded_centered_data h0q h0r (1/32) (by norm_num) (by norm_num) B
  obtain ⟨Nt,hNt,hterminal⟩ := exists_hillComplexDirichletGapTerminal_analytic_bound h0q h0r B
  refine ⟨max Nm (max Nc Nt),hNm.trans (le_max_left _ _),?_⟩
  intro U hUB k hk Q hQ A hbound
  have hkm : Nm≤k := (le_max_left _ _).trans hk
  have hkc : Nc≤k := (le_max_left _ _).trans ((le_max_right _ _).trans hk)
  have hkt : Nt≤k := (le_max_right _ _).trans ((le_max_right _ _).trans hk)
  have hk1 : 1≤k := hNm.trans hkm
  let c : ℂ := hillRealGapCenter 0 h0q h0r k
  let R := hillRealGapHalfLength 0 h0q h0r k+hillRealGapCollar 0 h0q h0r k
  let μ := hillScaledDirichletRoot h0q h0r (1/16) k
  let τ := hillLocalGapMidpoint 0 h0q h0r k
  have hR : 0<R := add_pos_of_nonneg_of_pos (hillRealGapContour_geometry 0 h0q h0r k hk1).1
    (hillRealGapContour_geometry 0 h0q h0r k hk1).2.1
  have hpB (p : Coeff 2) (hp : p∈U) : ‖p‖≤B :=
    (show ‖p‖<B by simpa only [mem_ball,dist_zero_right] using hUB hp).le
  have harg (p : Coeff 2) (hp : p∈U) : ‖μ p-τ p‖<R/8 := by
    have hm : ‖μ p-c‖<(1/16)*R := by simpa only [mem_ball,dist_eq_norm] using ((hmu k hkm).2 p (hpB p hp)).1
    have ht := ((hcenter k hkc).2.2 p (hpB p hp)).1
    have hh := norm_sub_le_norm_sub_add_norm_sub (μ p) c (τ p)
    rw [norm_sub_rev c (τ p)] at hh
    linarith
  have haQ (p : Coeff 2) (hp : p∈U) : AnalyticAt ℂ (fun p => Q (μ p-τ p,p)) p := by
    have hm := (hmu k hkm).1 p (hUB hp)
    have ht := (hcenter k hkc).1 p (hUB hp)
    have hw : μ p-τ p∈ball (0:ℂ) (R/4) := by
      rw [mem_ball,dist_zero_right]
      exact (harg p hp).trans (by linarith)
    exact (hQ (μ p-τ p,p) ⟨hw,hp⟩).comp
      (f := fun p : Coeff 2 => (μ p-τ p,p)) ((hm.sub ht).prod analyticAt_id)
  refine ⟨?_,?_⟩
  · intro p hp
    exact (analyticAt_const.mul ((hterminal k hkt).1 p (hUB hp))).mul (haQ p hp)
  · intro p hp
    rw [hillCenteredQuadraticDirichletValue,norm_mul,norm_mul,norm_I,one_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply hbound p hp (μ p-τ p)
    rw [mem_closedBall,dist_zero_right]
    exact (harg p hp).le

end NLS.KdV
