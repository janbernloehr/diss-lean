import NLS.ZakharovShabat.SourceAbelianCriticalCosineCancellation
import NLS.ZakharovShabat.SourceAbelianMomentErrorDomain
import NLS.ZakharovShabat.SourceMomentRegularFactorization

/-! # Critical cancellation in the actual off-diagonal second moment

The regular numerator includes the exact critical term with zero weighted
period. It splits into the actual root difference, the deleted-product
difference, and a term with an extra separated denominator. This is the
cancellation in equations (48) and Lemma 5.3 of the article.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Critical filling gives the actual regular psi factor on the gap itself. -/
theorem sourceMomentRegularNumerator_criticalFilled
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n k : ℤ) (hkn : k ≠ n) (a : DeletedCoeff p n)
    (ψ : CoeffPair p) (z : ℂ) (havoid : sourceCriticalRoot hp hp1 ψ n-z ≠ 0) :
    sourceMomentRegularNumerator hp hp1 n k (a : Coeff p) ψ z =
      I*(displacedRoots (a : Coeff p) k-z)*sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z/
        (sourceCriticalRoot hp hp1 ψ n-z) := by
  rw [← sourceMomentRegularNumerator_fillDeletedRoot hp hp1 n k a (sourceCriticalRoot hp hp1 ψ n),
    sourceMomentRegularNumerator_eq_gap_factor hp hp1 n k _ ψ z (by
      simpa only [displacedRoots_sourcePsiFillDeletedRoot_same] using havoid),
    displacedRoots_sourcePsiFillDeletedRoot_other n k hkn]
  unfold sourcePsiGapRegularFactor sourcePsiCriticalFilledQuotient
  rw [displacedRoots_sourcePsiFillDeletedRoot_same]
  ring

/-- The critically cancelled regular numerator of the scaled second moment. -/
def sourceSecondMomentCriticalNumerator (hp : p ≠ ⊤) (hp1 : 1 < p)
    (W : Set (CoeffPair p)) (n k : ℤ) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ) : ℂ :=
  (sourceCriticalRoot hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 ψ k)*
    sourceAbelianMomentEvenNumerator hp hp1 W n k 1 (a : Coeff p) ψ z+
      sourceFullAbelianSquare hp hp1 W k (z,ψ)*sourceCriticalRootGapNumerator hp hp1 ψ k z

/-- The exact numerator separates into the root error, product error and quadratic remainder. -/
theorem sourceSecondMomentCriticalNumerator_eq_three_terms
    (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p))
    (n k : ℤ) (hkn : k ≠ n) (a : DeletedCoeff p n) (ψ : CoeffPair p) (z : ℂ)
    (havoid : sourceCriticalRoot hp hp1 ψ n-z ≠ 0) :
    sourceSecondMomentCriticalNumerator hp hp1 W n k a ψ z =
      I*sourceFullAbelianSquare hp hp1 W k (z,ψ)*
        ((displacedRoots (a : Coeff p) k-sourceCriticalRoot hp hp1 ψ k)*
            sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z+
          (sourceCriticalRoot hp hp1 ψ k-z)*
            (sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z-sourceCriticalDeletedQuotient hp hp1 k ψ z)+
          (z-sourceStandardRootMidpoint hp hp1 ψ k)*(displacedRoots (a : Coeff p) k-z)*
            sourcePsiCriticalFilledQuotient hp hp1 n k a ψ z/(sourceCriticalRoot hp hp1 ψ n-z)) := by
  have hc : sourceCriticalRootGapNumerator hp hp1 ψ k z =
      -I*(sourceCriticalRoot hp hp1 ψ k-z)*sourceCriticalDeletedQuotient hp hp1 k ψ z := by
    simp only [sourceCriticalRootGapNumerator,sourceCriticalRootRatioExtension,
      sourceCriticalDeletedQuotient,sourceCriticalRoot]
    ring
  unfold sourceSecondMomentCriticalNumerator sourceAbelianMomentEvenNumerator
  rw [pow_one,sourceMomentRegularNumerator_criticalFilled hp hp1 n k hkn a ψ z havoid,hc]
  field_simp [havoid]
  ring

namespace SourceAbelianMomentErrorDomain
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W W' : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n} {A : SourceAbelianMomentAtlas hp hp1 W s}

/-- The actual critically cancelled numerator controls the scaled second moment
on the actual complex gap, including when the gap collapses. -/
theorem critical_comparison_bound
    (D : SourceAbelianMomentErrorDomain A)
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W')
    (ψ : CoeffPair p) (hψ : ψ ∈ D.domain)
    (hψC : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (n k : ℤ) (B : ℝ)
    (hB : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
      ‖sourceSecondMomentCriticalNumerator hp hp1 W n k (s n ψ) ψ z‖ ≤ B) :
    ‖(2*Real.pi:ℂ)⁻¹*((sourceCriticalRoot hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 ψ k)*
      A.moment n k 2 ψ)‖ ≤ B := by
  obtain ⟨φ,hφ⟩ := mem_iUnion.mp (D.source_subset hψ)
  obtain ⟨E⟩ := (A.localChart φ).charts ψ hφ
  obtain ⟨E'⟩ := C.charts ψ hψC
  let g : ℂ × CoeffPair p → ℂ := fun t =>
    -(sourceFullAbelianSquare hp hp1 W k t*sourceCriticalRootGapNumerator hp hp1 t.2 k t.1)
  have hSq : ContinuousOn (fun z => sourceFullAbelianSquare hp hp1 W k (z,ψ))
      (sourcePeriodicSegment hp hp1 ψ k) := by
    have he : (fun z => sourceFullAbelianSquare hp hp1 W k (z,ψ)) =
        fun z => sourceFullAbelianSquare hp hp1 W' k (z,ψ) :=
      funext (sourceFullAbelianSquare_independent_neighborhood E E' k)
    rw [he]
    exact (C.fullSquare_analytic k ψ hψC).continuousOn.mono (C.segment_subset_fullSquareDomain k ψ hψC)
  have hcrit : ContinuousOn (sourceCriticalRootGapNumerator hp hp1 ψ k)
      (sourcePeriodicSegment hp hp1 ψ k) :=
    (((analyticOnNhd_const.sub analyticOnNhd_id).mul (C.extension_analytic ψ hψC k)).continuousOn).mono
      (fun z hz => C.discs.avoids_other ψ hψC k (ball_subset_closedBall (C.segment_subset_outer k ψ hψC hz)))
  have hg : ContinuousOn (fun z => g (z,ψ)) (sourcePeriodicSegment hp hp1 ψ k) :=
    (hSq.mul hcrit).neg
  have hzero : sourceGapCosineMean hp hp1 k g ψ = 0 := by
    have hz := C.fullSquare_critical_cosineMean_eq_zero_of_chart ψ hψC E k
    unfold sourceGapCosineMean parametricCosineMean at hz ⊢
    simp only [g,intervalIntegral.integral_neg,hz,neg_zero]
  have hb := D.norm_model_error_le ψ hψ n k
    (sourceCriticalRoot hp hp1 ψ n-sourceStandardRootMidpoint hp hp1 ψ k) g hg B (by
      intro z hz
      simpa only [g,sub_neg_eq_add,sourceSecondMomentCriticalNumerator] using hB z hz)
  simpa only [hzero,mul_zero,sub_zero] using hb

end SourceAbelianMomentErrorDomain
end NLS.ZakharovShabat
