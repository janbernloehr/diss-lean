import NLS.ZakharovShabat.SourceFullAbelianGapBoundary
import NLS.ZakharovShabat.SourceAbelianMomentSquaredOffsetError

/-! # The vanishing short endpoint pieces in F.2

The actual side boundary value of the primitive is at most pi*M times
the gap norm when the regular factor is bounded by M and the critical
point is within half the gap of its midpoint. Both sides and collapsed
gaps are included.
-/
noncomputable section
open Set Metric Filter Topology Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SourceFullAbelianUniformCauchyFamily
variable {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
variable (C : SourceFullAbelianUniformCauchyFamily hp hp1 W)

/-- The short endpoint boundary piece has the explicit pi*M gap bound. -/
theorem appendixF_gapBoundary_norm_le_gap (ψ : CoeffPair p)
    (hψ : ψ ∈ ball C.discs.source.val C.discs.sourceRadius) (n : ℤ)
    (M : ℝ) (hM : 0 ≤ M)
    (hχ : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
      ‖sourceCriticalRootRatioExtension hp hp1 n ψ z‖ ≤ M)
    (hc : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
      sourceStandardRootMidpoint hp hp1 ψ n‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖/2)
    (θ : ℝ) (hθ : θ ∈ Icc 0 Real.pi) (upper : Bool) :
    ‖C.gapBoundary n ψ θ upper‖ ≤ Real.pi*M*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
  have hnum : ∀ z ∈ sourcePeriodicSegment hp hp1 ψ n,
      ‖sourceCriticalRootGapNumerator hp hp1 ψ n z‖ ≤
        ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*M := by
    intro z hz
    have hzmid := norm_sourceMidpoint_sub_le_halfGap hp hp1 ψ n z hz
    have hdist : ‖canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
        (periodOnePotential_mem ψ) n-z‖ ≤ ‖sourcePeriodicGapDisplacement hp hp1 ψ n‖ := by
      have h := norm_sub_le_norm_sub_add_norm_sub
        (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)
        (sourceStandardRootMidpoint hp hp1 ψ n) z
      linarith
    rw [sourceCriticalRootGapNumerator,norm_mul]
    exact mul_le_mul hdist (hχ z hz) (norm_nonneg _) (norm_nonneg _)
  have h := C.gapBoundary_norm_le n ψ hψ (‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*M)
    (mul_nonneg (norm_nonneg _) hM) hnum θ hθ upper
  nlinarith

/-- A common regular-factor bound makes all selected short pieces vanish as the gap collapses. -/
theorem appendixF_gapBoundary_tendsto_zero {ι : Type*} {l : Filter ι}
    (ψ : ι → CoeffPair p) (n : ℤ) (M : ℝ) (hM : 0 ≤ M)
    (θ : ι → ℝ) (upper : ι → Bool)
    (hdata : ∀ᶠ i in l,
      ψ i ∈ ball C.discs.source.val C.discs.sourceRadius ∧ θ i ∈ Icc 0 Real.pi ∧
      (∀ z ∈ sourcePeriodicSegment hp hp1 (ψ i) n,
        ‖sourceCriticalRootRatioExtension hp hp1 n (ψ i) z‖ ≤ M) ∧
      ‖canonicalCriticalPoints hp hp1 (periodOnePotential (ψ i)) (periodOnePotential_mem (ψ i)) n-
        sourceStandardRootMidpoint hp hp1 (ψ i) n‖ ≤
          ‖sourcePeriodicGapDisplacement hp hp1 (ψ i) n‖/2)
    (hgap : Tendsto (fun i => ‖sourcePeriodicGapDisplacement hp hp1 (ψ i) n‖) l (𝓝 0)) :
    Tendsto (fun i => C.gapBoundary n (ψ i) (θ i) (upper i)) l (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun _ => norm_nonneg _)) ?_
    (by simpa only [mul_zero] using hgap.const_mul (Real.pi*M))
  filter_upwards [hdata] with i hi
  exact C.appendixF_gapBoundary_norm_le_gap (ψ i) hi.1 n M hM hi.2.2.1 hi.2.2.2
    (θ i) hi.2.1 (upper i)

end SourceFullAbelianUniformCauchyFamily
end NLS.ZakharovShabat
