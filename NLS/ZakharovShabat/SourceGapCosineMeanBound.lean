import NLS.ZakharovShabat.SourceAbelianMomentComplexCosine

/-! # Bounds for complex-source moments on their actual gaps

The exact cosine representation gives the normalized supremum bound on
the moving complex segment, including collapsed segments. Bounds for the
filled square and regular psi factor can therefore be combined directly.
-/
noncomputable section
open Set Metric Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The cosine integral has total angle length pi, for arbitrary complex
gap endpoints and without any regularity assumption on the numerator. -/
theorem norm_sourceGapCosineMean_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (g : ℂ × CoeffPair p → ℂ)
    (ψ : CoeffPair p) (M : ℝ)
    (hbound : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖g (z,ψ)‖ ≤ M) :
    ‖sourceGapCosineMean hp hp1 k g ψ‖ ≤ M*Real.pi := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0:ℝ)) (b := Real.pi)
    (f := fun θ => g (sourceStandardRootMidpoint hp hp1 ψ k +
      sourceStandardRootHalfGap hp hp1 ψ k * (Real.cos θ:ℂ),ψ)) (C := M) (by
      intro θ _
      apply hbound
      rw [sourcePeriodicSegment_eq_midpoint_segment]
      simpa only [cosineGapPoint,← Complex.ofReal_cos] using
        cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ k)
          (sourceStandardRootHalfGap hp hp1 ψ k) θ)
  simpa only [sourceGapCosineMean,parametricCosineMean,sub_zero,abs_of_pos Real.pi_pos] using hb

/-- After the moment normalization, the cosine representation has norm
at most the supremum of its regular numerator on the actual complex gap. -/
theorem norm_normalized_sourceGapCosineMean_le
    (hp : p ≠ ⊤) (hp1 : 1 < p) (k : ℤ) (g : ℂ × CoeffPair p → ℂ)
    (ψ : CoeffPair p) (M : ℝ)
    (hbound : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖g (z,ψ)‖ ≤ M) :
    ‖(2*Real.pi:ℂ)⁻¹ * (-(2*Complex.I) * sourceGapCosineMean hp hp1 k g ψ)‖ ≤ M := by
  have hn : ‖(2*Real.pi:ℂ)⁻¹ * (-(2*Complex.I))‖ = Real.pi⁻¹ := by
    simp [Real.pi_pos.le,mul_inv_rev]
  rw [← mul_assoc,norm_mul,hn]
  have hb := mul_le_mul_of_nonneg_left (norm_sourceGapCosineMean_le hp hp1 k g ψ M hbound)
    (inv_nonneg.mpr Real.pi_pos.le)
  calc
    _ ≤ Real.pi⁻¹ * (M*Real.pi) := hb
    _ = M := by field_simp

namespace SourceAbelianMomentAtlas
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
variable {s : (n : ℤ) → CoeffPair p → DeletedCoeff p n}

/-- Near every real source, the second moment satisfies the square-times-
regular-factor bound on the actual complex gap. The radius depends on
`n,k`, but works for every pair of pointwise bounds on that source ball. -/
theorem exists_ball_second_moment_norm_le
    (A : SourceAbelianMomentAtlas hp hp1 W s)
    (hs : SourcePsiNormalizedComplexExtension hp hp1 V s) (hV : IsOpen V)
    (φ : realTypeSourceSubmodule p) (hφ : φ.val ∈ V) (n k : ℤ) :
    ∃ r : ℝ, 0 < r ∧ ball φ.val r ⊆ A.domain ∩ V ∧ ∀ ψ ∈ ball φ.val r,
      ∀ M B : ℝ, 0 ≤ M → 0 ≤ B →
      (∀ z ∈ sourcePeriodicSegment hp hp1 ψ k, ‖sourceFullAbelianSquare hp hp1 W k (z,ψ)‖ ≤ M) →
      (∀ z ∈ sourcePeriodicSegment hp hp1 ψ k,
        ‖sourceMomentRegularNumerator hp hp1 n k (s n ψ : Coeff p) ψ z‖ ≤ B) →
      ‖(2*Real.pi:ℂ)⁻¹ * A.moment n k 2 ψ‖ ≤ M*B := by
  obtain ⟨r,hr,hsub,heq⟩ := A.exists_ball_second_moment_eq_cosineMean hs hV φ hφ n k
  refine ⟨r,hr,hsub,?_⟩
  intro ψ hψ M B hM _ hS hP
  rw [heq ψ hψ]
  apply norm_normalized_sourceGapCosineMean_le
  intro z hz
  simpa only [sourceAbelianMomentEvenNumerator,pow_one,norm_mul] using
    mul_le_mul (hS z hz) (hP z hz) (norm_nonneg _) hM

end SourceAbelianMomentAtlas
end NLS.ZakharovShabat
