import NLS.ComplexAnalysis.QuadraticPrimitiveGapComparison
import NLS.ZakharovShabat.SourceFullAbelianGapBoundary
import NLS.ZakharovShabat.SourceCriticalRootGapUniformBound

/-! # The quantitative gap comparison underlying Lemma 19.4

The error between the actual primitive and `i*w_n` has both gap-side
limits. Its boundary norm is controlled by the deleted critical factor's
error and the critical point's displacement from the midpoint. The
locally uniform form retains the exact squared-gap quotient, ready for
the sequence-space estimates in Lemma 19.4.
-/
noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Both boundary values of the standard root, in the oriented gap coordinate. -/
def sourceStandardRootGapBoundary (hp : p ≠ ⊤) (hp1 : 1 < p) (ψ : CoeffPair p)
    (j : ℤ) (θ : ℝ) (upper : Bool) : ℂ :=
  (if upper then -I else I)*(sourceStandardRootHalfGap hp hp1 ψ j*(Real.sin θ:ℂ))

theorem sourceStandardRoot_tendsto_gapBoundary (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (j : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    Tendsto (sourceStandardRoot hp hp1 ψ j)
      (𝓝[sourceAbelianGapSide hp hp1 ψ j upper]
        (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)))
      (𝓝 (sourceStandardRootGapBoundary hp hp1 ψ j θ upper)) := by
  cases upper
  · simpa only [sourceStandardRootGapBoundary,sourceAbelianGapSide,Bool.false_eq_true,
      ↓reduceIte,mul_assoc,mul_comm,mul_left_comm] using
      sourceStandardRoot_tendsto_gap_lower_cos hp hp1 ψ j θ hgap hθ.1 hθ.2
  · simpa only [sourceStandardRootGapBoundary,sourceAbelianGapSide,↓reduceIte,
      neg_mul,mul_neg,mul_assoc,mul_comm,mul_left_comm] using
      sourceStandardRoot_tendsto_gap_upper_cos hp hp1 ψ j θ hgap hθ.1 hθ.2

/-- The numerator defect separates into the deleted-factor error and
the critical-midpoint offset, with their original normalizations. -/
theorem sourceCriticalRootGapNumerator_sub_linear (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (j : ℤ) (z : ℂ) :
    sourceCriticalRootGapNumerator hp hp1 ψ j z-(z-sourceStandardRootMidpoint hp hp1 ψ j)*I =
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z)*
        (sourceCriticalRootRatioExtension hp hp1 j ψ z+I)-
      I*(canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-
        sourceStandardRootMidpoint hp hp1 ψ j) := by
  unfold sourceCriticalRootGapNumerator
  ring

/-- The error in the regular factor has exactly the norm of `chi_n-1`. -/
theorem norm_sourceCriticalRootRatioExtension_add_I (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (j : ℤ) (z : ℂ) :
    ‖sourceCriticalRootRatioExtension hp hp1 j ψ z+I‖ =
      ‖sourceSingleRootQuotientJointProduct hp hp1 j
        (z,(canonicalCriticalDisplacement hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ),ψ))-1‖ := by
  unfold sourceCriticalRootRatioExtension
  rw [show ∀ q : ℂ, -I*q+I = -I*(q-1) by intro q; ring]
  simp only [norm_mul,norm_neg,norm_I,one_mul]

/-- The zero-potential clause of Lemma 19.4 is exact everywhere. -/
theorem sourceFullAbelianPrimitive_zero_eq_I_mul_standardRoot
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (D : SourceAbelianSpectralChart hp hp1 W 0) (j : ℤ) (z : ℂ) :
    sourceFullAbelianPrimitive hp hp1 W j (z,0) = I*sourceStandardRoot hp hp1 0 j z := by
  rw [sourceFullAbelianPrimitive_zero D,sourceStandardRoot_of_zeroGap hp hp1 0 j z
    (by simpa only [map_zero] using canonicalPeriodicGap_zero hp hp1 j)]
  simp only [map_zero,canonicalPeriodicMidpoint_zero]
  ring

namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}

/-- The primitive-minus-root error has the claimed limits on both sides
of every noncollapsed gap, including its endpoints. -/
theorem fullPrimitive_sub_root_tendsto_gapBoundary
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j ≠ 0)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    Tendsto (fun z => sourceFullAbelianPrimitive hp hp1 W j (z,ψ)-I*sourceStandardRoot hp hp1 ψ j z)
      (𝓝[sourceAbelianGapSide hp hp1 ψ j upper]
        (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)))
      (𝓝 (C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper)) :=
  (C.fullPrimitive_tendsto_gapBoundary j ψ hψ hgap θ hθ upper).sub
    ((sourceStandardRoot_tendsto_gapBoundary hp hp1 ψ j hgap θ hθ upper).const_mul I)

/-- The filled primitive-minus-root error is zero at a collapsed gap. -/
theorem fullPrimitive_sub_root_eq_zero_of_collapsed
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j = 0)
    (θ : ℝ) :
    let z := sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ)
    sourceFullAbelianPrimitive hp hp1 W j (z,ψ)-I*sourceStandardRoot hp hp1 ψ j z = 0 := by
  dsimp only
  rw [C.fullPrimitive_eq_gapBoundary_of_collapsed j ψ hψ hgap θ true,
    C.gapBoundary_eq_zero_of_collapsed j ψ hgap θ true,
    sourceStandardRoot_of_zeroGap hp hp1 ψ j _ hgap]
  simp only [sourceStandardRootHalfGap,hgap,zero_div,zero_mul,add_zero,
    sourceStandardRootMidpoint,sub_self,mul_zero]

/-- A numerator-defect bound controls the actual primitive-minus-root
boundary error, on both sides and also for a collapsed gap. -/
theorem gapBoundary_sub_root_norm_le
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
      ‖sourceCriticalRootGapNumerator hp hp1 ψ j z-(z-sourceStandardRootMidpoint hp hp1 ψ j)*I‖ ≤ B)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤ B*Real.pi := by
  obtain ⟨E⟩ := C.charts ψ hψ
  have hseg := C.segment_subset_outer j ψ hψ
  rw [sourcePeriodicSegment_eq_midpoint_segment] at hseg hb
  have heq := sourceFullAbelianCauchyQuotient_equation hp hp1 W ψ j _ _
    ((C.discs.inner_pos j).trans (C.discs.inner_lt j)) E (C.circle_root j ψ hψ)
    (C.discs.avoids_other ψ hψ j) (C.extension_analytic ψ hψ j)
  have hpoly : (sourceStandardRootHalfGap hp hp1 ψ j)^2 =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j)^2/4 := by
    unfold sourceStandardRootHalfGap
    ring
  have h := norm_sine_mul_sub_of_quadratic_equation _ _ _ _ I _ hseg
    (C.quotient_slice_analytic j ψ hψ)
    (by simpa only [hpoly,sourceAngularSelectedPolynomial] using heq) B hB hb θ hθ
  have he : C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper =
      (if upper then -I else I)*(sourceStandardRootHalfGap hp hp1 ψ j*(Real.sin θ:ℂ)*
        (sourceFullAbelianCauchyQuotient hp hp1 W j (C.discs.center j) (C.discs.outer j)
          (sourceStandardRootMidpoint hp hp1 ψ j+sourceStandardRootHalfGap hp hp1 ψ j*(Real.cos θ:ℂ),ψ)-I)) := by
    unfold gapBoundary sourceStandardRootGapBoundary
    ring
  rw [he]
  cases upper <;> simpa only [Bool.false_eq_true,↓reduceIte,norm_mul,norm_neg,norm_I,one_mul] using h

/-- Separate control of the critical distance and deleted-factor error
gives the comparison bound used in Lemma 19.4. -/
theorem gapBoundary_sub_root_norm_le_of_factor_error
    (C : SourceFullAbelianUniformCauchyFamily hp hp1 W) (j : ℤ)
    (ψ : CoeffPair p) (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius)
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E)
    (hd : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j,
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-z‖ ≤ D)
    (he : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ j, ‖sourceCriticalRootRatioExtension hp hp1 j ψ z+I‖ ≤ E)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    ‖C.gapBoundary j ψ θ upper-I*sourceStandardRootGapBoundary hp hp1 ψ j θ upper‖ ≤
      (D*E+‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) j-
        sourceStandardRootMidpoint hp hp1 ψ j‖)*Real.pi := by
  apply C.gapBoundary_sub_root_norm_le j ψ hψ _ (by positivity) _ θ hθ upper
  intro z hz
  rw [sourceCriticalRootGapNumerator_sub_linear]
  apply (norm_sub_le _ _).trans
  simp only [norm_mul,norm_I,one_mul]
  exact add_le_add (mul_le_mul (hd z hz) (he z hz) (norm_nonneg _) hD) le_rfl

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
