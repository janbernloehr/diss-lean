import NLS.ZakharovShabat.SourceFiniteGapExteriorPeriod
import NLS.ComplexAnalysis.ExteriorHolomorphicPrimitive

/-! # A single-valued exterior primitive at actual finite-gap sources -/
noncomputable section
open Set Complex Metric NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- An actual finite-gap source has a primitive of the regularized quotient
on the full exterior of some disc. There is no supplied period hypothesis. -/
theorem exists_sourceFiniteGap_exterior_primitive (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : realTypeSourceLocus p) (hf : φ ∈ sourceFiniteGapLocus hp hp1) :
    ∃ R : ℝ, 0 < R ∧ ∃ F : ℂ → ℂ,
      ∀ z : ℂ, R < ‖z‖ → HasDerivAt F (sourceFloquetLogDerivative hp hp1 φ.val z) z := by
  obtain ⟨T, hT, hperiod⟩ := exists_sourceFiniteGap_exterior_period_zero hp hp1 φ hf
  obtain ⟨A, _, hA⟩ := exists_exterior_subset_sourceOpenGapComplement_finiteGap hp hp1 φ hf
  let R := max T A + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_left T A]
  have hTR : T ≤ R := by dsimp [R]; linarith [le_max_left T A]
  have hAR : A < R := by dsimp [R]; linarith [le_max_right T A]
  have ha : AnalyticOnNhd ℂ (sourceFloquetLogDerivative hp hp1 φ.val) (ball 0 R)ᶜ := by
    apply (sourceFloquetLogDerivative_analyticOnNhd hp hp1 φ.val φ.property).mono
    intro z hz
    apply hA
    have hzR : R ≤ ‖z‖ := by simpa only [mem_compl_iff, mem_ball, dist_zero_right, not_lt] using hz
    exact hAR.trans_le hzR
  obtain ⟨F, hF⟩ := exists_primitive_on_exterior_of_zero_period
    (sourceFloquetLogDerivative hp hp1 φ.val) 0 R hR ha (hperiod R hTR)
  refine ⟨R, hR, F, ?_⟩
  intro z hz
  exact hF z (by simpa only [mem_closedBall, dist_zero_right, not_le] using hz)

end NLS.ZakharovShabat
