import NLS.ZakharovShabat.SourceNormalizedActionFactorContinuity
import NLS.ZakharovShabat.SourceNormalizedActionTailBound

/-!
# A tail bound across open and collapsed real-type gaps

The cosine formula controls the normalized action on open gaps. At a
collapsed gap, its continuous extension is the deleted spectral factor
at the midpoint. The same product-tail estimate therefore controls
the extension without an open-gap qualification.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The product-tail bound on the cosine path also bounds the
collapsed value prescribed by the cosine moment. -/
theorem exists_local_sourceNormalizedActionCollapsedCandidate_tail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ,
        ∀ ψ ∈ V, ∀ n : ℤ, K ≤ n.natAbs →
          ‖4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ - 1‖ ≤
            sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := by
  obtain ⟨V,hVopen,hφV,C,hC,K,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_tail_bound hp hp1 φ hφ
  refine ⟨V,hVopen,hφV,C,hC,K,?_⟩
  intro ψ hψ n hn
  have hmid := hfactor ψ hψ n hn (Real.pi/2)
  have hvalue : 4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ =
      I * sourceCriticalRootRatioExtension hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n) := by
    simp only [sourceNormalizedActionCollapsedCandidate]
    ring
  rw [hvalue]
  simpa only [Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero,
    add_zero] using hmid

/-- The continuous real-type extension satisfies one quantitative
product-tail estimate at every sufficiently distant gap, including
collapsed gaps. -/
theorem exists_local_sourceNormalizedActionRealExtension_tail_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧
      ∃ C : ℝ, 1 ≤ C ∧ ∃ K : ℕ,
        ∀ ψ ∈ V, IsRealType (CoeffPair.toMax p ψ) →
          ∀ n : ℤ, K ≤ n.natAbs →
            ‖4 * sourceNormalizedActionRealExtension hp hp1 n ψ - 1‖ ≤
              8 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2 *
                ‖sourceCriticalGapQuotient hp hp1 ψ n‖^2 +
              2 * (2 * ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ *
                ‖sourceCriticalGapQuotient hp hp1 ψ n‖ + 1)^2 *
                  sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := by
  obtain ⟨V,hVopen,hφV,C,hC,K,hfactor⟩ :=
    exists_local_sourceNormalizedAction_factor_tail_bound hp hp1 φ hφ
  refine ⟨V,hVopen,hφV,C,hC,K,?_⟩
  intro ψ hψ hreal n hn
  by_cases hgap : sourcePeriodicGapDisplacement hp hp1 ψ n = 0
  · have hmid := hfactor ψ hψ n hn (Real.pi/2)
    have hbound : ‖4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ - 1‖ ≤
        sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := by
      have hvalue : 4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ =
          I * sourceCriticalRootRatioExtension hp hp1 n ψ
            (sourceStandardRootMidpoint hp hp1 ψ n) := by
        simp only [sourceNormalizedActionCollapsedCandidate]
        ring
      rw [hvalue]
      simpa only [Real.cos_pi_div_two, Complex.ofReal_zero, mul_zero,
        add_zero] using hmid
    have hmajor : 0 ≤ sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n :=
      (norm_nonneg _).trans hbound
    simp only [sourceNormalizedActionRealExtension, hgap,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero,
      zero_add]
    calc
      ‖4 * sourceNormalizedActionCollapsedCandidate hp hp1 n ψ - 1‖ ≤
          sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := hbound
      _ ≤ 2 * 1^2 *
          sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n := by
        nlinarith
  · have hopen := source_openRealGap_of_realType_gap_ne_zero
      hp hp1 n ψ hreal hgap
    have hbound := norm_sourceRawNormalizedAction_sub_one_le_of_factor_bound
      hp hp1 ψ hreal n hopen
      (sourceNormalizedActionFactorTailMajorant hp hp1 C ψ n)
      (hfactor ψ hψ n hn)
    simpa only [sourceNormalizedActionRealExtension, if_neg hgap] using hbound

end NLS.ZakharovShabat
