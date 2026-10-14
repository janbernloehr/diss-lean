import NLS.ZakharovShabat.SourceEquation2_19
import NLS.ZakharovShabat.SourceActionChiGapSup
import NLS.ZakharovShabat.SourceNormalizedActionEstimate

/-!
# The normalized action estimate at arbitrary complex sources

The filled indexed action has the same cosine model even at collapsed
gaps. Its deviation from one is controlled by the actual critical offset
and the literal gap supremum on the entire original source domain.
-/

noncomputable section
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Every point of the cosine path lies in the actual complex segment. -/
theorem sourceActionChi_cosinePoint_mem_gap (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (n : ℤ) (θ : ℝ) :
    sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ) ∈
      sourcePeriodicSegment hp hp1 ψ n := by
  rw [sourcePeriodicSegment_eq_midpoint_segment]
  simpa only [cosineGapPoint,← Complex.ofReal_cos] using
    cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) θ

/-- The complementary factor along the cosine path is continuous for complex sources. -/
theorem SourceEquation2_18Data.chi_cosine_continuous
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    Continuous (fun θ : ℝ => sourceActionChi hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))) := by
  apply continuousOn_univ.mp
  apply (H.chi_continuousOn_gap ψ hψ n).comp (by fun_prop : ContinuousOn
    (fun θ : ℝ => sourceStandardRootMidpoint hp hp1 ψ n+
      sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ)) univ)
  exact fun θ _ => sourceActionChi_cosinePoint_mem_gap hp hp1 ψ n θ

/-- The filled normalized action has the cosine representation even at zero gaps. -/
theorem SourceEquation2_19Data.normalized_eq_cosineModel
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    4*sourceNormalizedIndexedAction hp hp1 n ψ =
      normalizedActionCosineModel (sourceActionCriticalCoordinate hp hp1 n ψ)
        (fun θ => sourceActionChi hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))) := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · have hu : sourceActionCriticalCoordinate hp hp1 n ψ = 0 := by
      rw [H.previous.actionCriticalCoordinate_eq_gap_mul ψ hψ n,hg]
      simp
    have hd : sourceStandardRootHalfGap hp hp1 ψ n = 0 := by
      simp only [sourceStandardRootHalfGap,hg,zero_div]
    rw [sourceNormalizedIndexedAction_eq_collapsed hp hp1 n ψ hg]
    simp only [normalizedActionCosineModel,hu,hd,zero_mul,add_zero]
    rw [intervalIntegral.integral_mul_const,integral_shifted_cos_sq_complex]
    have hpi : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    field_simp
    ring
  · rw [sourceNormalizedIndexedAction_eq_quotient hp hp1 n ψ hg,← mul_div_assoc,
      H.normalized_integral ψ hψ n hg]
    unfold normalizedActionCosineModel
    congr 1
    calc
      _ = ∫ t in (-1:ℝ)..1,
          ((sourceActionCriticalCoordinate hp hp1 n ψ-(t:ℂ))^2*
            sourceActionChi hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))) /
                (Real.sqrt (1-t^2):ℂ) := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := integral_div_sqrt_one_sub_sq_eq_cosine _

/-- The source's normalized-action error is bounded on all of W, including collapse. -/
theorem SourceEquation2_19Data.norm_normalized_sub_one_le
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    ‖4*sourceNormalizedIndexedAction hp hp1 n ψ-1‖ ≤
      8*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖^2*‖sourceCriticalGapQuotient hp hp1 ψ n‖^2+
      2*(2*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*‖sourceCriticalGapQuotient hp hp1 ψ n‖+1)^2*
        sourceActionChiGapSup hp hp1 ψ n := by
  let u := sourceActionCriticalCoordinate hp hp1 n ψ
  let χ : ℝ → ℂ := fun θ => sourceActionChi hp hp1 n ψ
    (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(Real.cos θ:ℂ))
  have hu : ‖u‖ = 2*‖sourcePeriodicGapDisplacement hp hp1 ψ n‖*‖sourceCriticalGapQuotient hp hp1 ψ n‖ := by
    dsimp only [u]
    rw [H.previous.actionCriticalCoordinate_eq_gap_mul ψ hψ n,← sourcePeriodicGapDisplacement_apply]
    simp
  have he := norm_normalizedActionCosineModel_sub_le u χ
    ((H.previous.chi_cosine_continuous ψ hψ n).intervalIntegrable _ _)
      (sourceActionChiGapSup hp hp1 ψ n)
      (fun θ => H.previous.norm_chi_sub_one_le_gapSup ψ hψ n _
        (sourceActionChi_cosinePoint_mem_gap hp hp1 ψ n θ))
  rw [H.normalized_eq_cosineModel ψ hψ n]
  have hsplit : normalizedActionCosineModel u χ-1 =
      (normalizedActionCosineModel u χ-(1+2*u^2))+2*u^2 := by ring
  change ‖normalizedActionCosineModel u χ-1‖ ≤ _
  rw [hsplit]
  calc
    _ ≤ ‖normalizedActionCosineModel u χ-(1+2*u^2)‖+‖2*u^2‖ := norm_add_le _ _
    _ ≤ 2*(‖u‖+1)^2*sourceActionChiGapSup hp hp1 ψ n+2*‖u‖^2 := by
      have hn : ‖(2:ℂ)*u^2‖ = 2*‖u‖^2 := by simp
      rw [← hn]
      exact add_le_add he le_rfl
    _ = _ := by rw [hu]; ring

end NLS.ZakharovShabat
