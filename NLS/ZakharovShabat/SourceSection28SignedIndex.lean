import NLS.ZakharovShabat.SourceSection28GapBounds
import NLS.ZakharovShabat.Lemma281BoundaryArithmetic

/-! # The negative-index ratio in the literal statement of Lemma 28.1

The printed hypothesis allows negative n, but its first rational bound uses
n without an absolute value. At n=-1 and N=1 the right-hand side is negative,
whereas the actual zero-source deleted product is one. This refutes that
intermediate bound, not the independently proved final constant 2048.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The literal signed-index ratio fails at the actual zero source and its collapsed gap. -/
theorem SourceEquation2_19Data.section28_signed_ratio_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (hzero : (0 : CoeffPair p) ∈ W) :
    ¬ ‖sourceActionChi hp hp1 (-1) (0 : CoeffPair p)
      (sourceStandardRootMidpoint hp hp1 0 (-1))‖ ≤
        128*((-1:ℝ)+1+2/5)/((-1:ℝ)-1+3/10) := by
  have hz := H.previous.segment_subset_omitted (0 : CoeffPair p) hzero (-1)
    (sourcePeriodicMidpoint_mem_segment hp hp1 0 (-1))
  rw [sourceActionChi_zero_source hp hp1 (-1) _ hz]
  norm_num

/-- The counterexample satisfies the printed cutoff in the exact physical H¹ norm. -/
theorem section28_zero_physical_cutoff :
    (1+|(-1:ℝ)| ≥ 1+|(1:ℝ)|) ∧
      (1+|(1:ℝ)| ≥ 8*‖sourcePhysicalH1Coordinates (0 : ScalarDomain 2 × ScalarDomain 2)‖^2) := by
  have hz : sourcePhysicalH1Coordinates (0 : ScalarDomain 2 × ScalarDomain 2) = 0 := by
    apply (CoeffPair.toMax 2).injective
    apply Prod.ext <;> ext n <;> simp
  rw [hz]
  norm_num

/-- Every retained original family contains the zero-source witness. -/
theorem SourceSection27Data.section28_signed_ratio_counterexample
    {W₀ W V Wa B U T : Set (CoeffPair 2)} {s : (n : ℤ) → CoeffPair 2 → DeletedCoeff 2 n}
    {D : SourceSection17OriginalData (by simp) (by norm_num) W₀ W V s}
    {A : SourceAbelianMomentAtlas (by simp) (by norm_num) Wa s}
    (Q : SourceSection27Data D A B U T) :
    (0 : CoeffPair 2) ∈ U ∩ T ∧
    ¬ ‖sourceActionChi (by simp) (by norm_num) (-1) (0 : CoeffPair 2)
      (sourceStandardRootMidpoint (by simp) (by norm_num) (0 : CoeffPair 2) (-1))‖ ≤
        128*((-1:ℝ)+1+2/5)/((-1:ℝ)-1+3/10) := by
  have hz : (0 : CoeffPair 2) ∈ realTypeSourceLocus 2 := by simp [realTypeSourceLocus]
  refine ⟨⟨Q.real_subset hz,Q.gap_real_subset hz⟩,?_⟩
  exact D.section28_gapFormulas.section28_signed_ratio_zero
    (D.previous.previous.previous.subset (D.complex.source_subset (Q.original_subset (Q.real_subset hz))))

end NLS.ZakharovShabat
