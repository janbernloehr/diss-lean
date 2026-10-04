import NLS.ZakharovShabat.SourceGapCosinePolynomial
import NLS.ZakharovShabat.SourceFullAbelianSquareGapBound

/-! # Quantitative errors from regular cosine numerators

Subtracting a polynomial model before integration preserves its exact
cancellation. The normalized error is bounded by the numerator error on
the actual complex gap, including a collapsed gap.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Continuity on the actual gap suffices for its regular cosine integral. -/
theorem intervalIntegrable_sourceGapCosineNumerator
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (ψ : CoeffPair p) (g : ℂ × CoeffPair p → ℂ)
    (hg : ContinuousOn (fun z => g (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k)) :
    IntervalIntegrable (fun θ : ℝ => g (sourceStandardRootMidpoint hp hp1 ψ k+
      sourceStandardRootHalfGap hp hp1 ψ k*(Real.cos θ:ℂ),ψ)) MeasureTheory.volume 0 Real.pi := by
  apply ContinuousOn.intervalIntegrable
  apply hg.comp (by fun_prop)
  intro θ _
  rw [sourcePeriodicSegment_eq_midpoint_segment]
  simpa only [cosineGapPoint,← Complex.ofReal_cos] using
    cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ k)
      (sourceStandardRootHalfGap hp hp1 ψ k) θ

/-- The normalized difference is controlled by the pointwise numerator
error, with the same constant at open and collapsed complex gaps. -/
theorem norm_sourceGapCosineMean_sub_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (ψ : CoeffPair p)
    (g h : ℂ × CoeffPair p → ℂ)
    (hg : ContinuousOn (fun z => g (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k))
    (hh : ContinuousOn (fun z => h (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k))
    (B : ℝ) (hB : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖g (z,ψ)-h (z,ψ)‖ ≤ B) :
    ‖(2*Real.pi:ℂ)⁻¹ * (-(2*Complex.I) *
      (sourceGapCosineMean hp hp1 k g ψ-sourceGapCosineMean hp hp1 k h ψ))‖ ≤ B := by
  have he : sourceGapCosineMean hp hp1 k (fun t => g t-h t) ψ =
      sourceGapCosineMean hp hp1 k g ψ-sourceGapCosineMean hp hp1 k h ψ := by
    unfold sourceGapCosineMean parametricCosineMean
    exact intervalIntegral.integral_sub
      (intervalIntegrable_sourceGapCosineNumerator hp hp1 k ψ g hg)
      (intervalIntegrable_sourceGapCosineNumerator hp hp1 k ψ h hh)
  rw [← he]
  exact norm_normalized_sourceGapCosineMean_le hp hp1 k _ ψ B hB

/-- The selected quadratic is bounded by one quarter of the squared gap
length throughout the complex segment. -/
theorem norm_sourceAngularSelectedPolynomial_le_gap_sq
    (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p) (k : ℤ)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment hp hp1 ψ k) :
    ‖sourceAngularSelectedPolynomial hp hp1 ψ k z‖ ≤
      ‖sourcePeriodicGapDisplacement hp hp1 ψ k‖^2/4 := by
  rw [← sourceStandardRoot_gapSegment_eq_periodicSegment hp hp1 ψ k] at hz
  obtain ⟨t,ht,rfl⟩ := hz
  have hcos : Real.cos (Real.arccos t) = t := Real.cos_arccos ht.1 ht.2
  rw [← hcos,← sourceStandardRootGapBoundary_sq hp hp1 ψ k (Real.arccos t) true,norm_pow]
  have h := norm_sourceStandardRootGapBoundary_le_halfGap hp hp1 ψ k (Real.arccos t) true
  nlinarith [norm_nonneg (sourceStandardRootGapBoundary hp hp1 ψ k (Real.arccos t) true)]

/-- Multiplying the square and regular-factor expansions gives the
explicit error constant used by both diagonal and off-diagonal moments. -/
theorem norm_square_regular_product_error_le
    (S P R : ℂ) (H E F : ℝ) (hH : 0 ≤ H) (hE : 0 ≤ E)
    (hS : ‖S+P‖ ≤ H*E) (hP : ‖P‖ ≤ H/4) (hR : ‖R-Complex.I‖ ≤ F) :
    ‖S*R+Complex.I*P‖ ≤ H*(E*(F+1)+F/4) := by
  have hRnorm : ‖R‖ ≤ F+1 := by
    calc
      ‖R‖ = ‖(R-Complex.I)+Complex.I‖ := by congr 1; ring
      _ ≤ ‖R-Complex.I‖+1 := by simpa only [norm_I] using norm_add_le (R-Complex.I) Complex.I
      _ ≤ F+1 := add_le_add hR le_rfl
  have he : S*R+Complex.I*P = (S+P)*R-P*(R-Complex.I) := by ring
  rw [he]
  calc
    _ ≤ ‖S+P‖*‖R‖+‖P‖*‖R-Complex.I‖ := by simpa only [norm_mul] using norm_sub_le ((S+P)*R) (P*(R-Complex.I))
    _ ≤ (H*E)*(F+1)+(H/4)*F := add_le_add
      (mul_le_mul hS hRnorm (norm_nonneg _) (mul_nonneg hH hE))
      (mul_le_mul hP hR (norm_nonneg _) (div_nonneg hH (by norm_num)))
    _ = _ := by ring

end NLS.ZakharovShabat
