import NLS.ZakharovShabat.SourceActionChiCosine
import NLS.ComplexAnalysis.ComplexArcsineIntegral

/-!
# Equation (2.19) for complex potentials on the original domain

The actual indexed action is an arcsine-weighted integral along the
actual complex gap. All integrals are proved integrable, including at
their endpoint singularities. Normalization is asserted off the actual
zero-gap set; neither a real-source assumption nor a domain shrink is used.
-/

noncomputable section
open Set Metric Complex MeasureTheory NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Continuity of the literal deleted product along the full complex gap. -/
theorem SourceEquation2_18Data.chi_gap_continuous
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    ContinuousOn (fun t : ℝ => sourceActionChi hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))) (Icc (-1) 1) := by
  have hm : Continuous (fun t : ℝ =>
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ),ψ)) := by fun_prop
  apply (H.joint n).continuousOn.comp hm.continuousOn
  intro t ht
  refine ⟨hψ,H.segment_subset_omitted ψ hψ n ?_⟩
  rw [sourcePeriodicSegment_eq_midpoint_segment]
  simpa only [cosineGapPoint,← Complex.ofReal_cos,Real.cos_arccos ht.1 ht.2] using
    cosineGapPoint_real_mem_segment (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) (Real.arccos t)

/-- The numerator in either weighted formula is continuous before division by the weight. -/
theorem SourceEquation2_18Data.chi_gap_weighted_integrable
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) (a b : ℂ) :
    IntervalIntegrable (fun t : ℝ => (a-b*(t:ℂ))^2/(Real.sqrt (1-t^2):ℂ)*
      sourceActionChi hp hp1 n ψ
        (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))) volume (-1) 1 := by
  have hc : ContinuousOn (fun t : ℝ => (a-b*(t:ℂ))^2*sourceActionChi hp hp1 n ψ
      (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))) (Icc (-1) 1) :=
    (by fun_prop : Continuous (fun t : ℝ => (a-b*(t:ℂ))^2)).continuousOn.mul
      (H.chi_gap_continuous ψ hψ n)
  convert intervalIntegrable_div_sqrt_one_sub_sq hc using 1
  funext t
  ring

/-- The weighted gap integral immediately preceding (2.19), even at a collapsed gap. -/
theorem SourceEquation2_18Data.action_eq_chi_gapIntegral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W) (hWc : IsPreconnected W)
    (hR : realTypeSourceLocus p ⊆ W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ = (2/(Real.pi:ℂ)) * ∫ t in (-1:ℝ)..1,
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))^2 /
        (Real.sqrt (1-t^2):ℂ)*sourceActionChi hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ)) := by
  rw [H.action_eq_chiCosineMean hW hWc hR n hψ]
  unfold sourceGapCosineMean parametricCosineMean
  dsimp only
  rw [← integral_div_sqrt_one_sub_sq_eq_cosine (fun t : ℝ => sourceActionChiNumerator hp hp1 n
    (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ),ψ))]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only [sourceActionChiNumerator]
  ring

/-- The normalized critical coordinate t_n printed in (2.19). -/
def sourceActionCriticalCoordinate (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) : ℂ :=
  (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
    sourceStandardRootMidpoint hp hp1 ψ n) / sourceStandardRootHalfGap hp hp1 ψ n

/-- Lemma 10.10 gives the exact t_n=2γ_n B_n identity, also at a collapsed gap. -/
theorem SourceEquation2_18Data.actionCriticalCoordinate_eq_gap_mul
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceActionCriticalCoordinate hp hp1 n ψ =
      2*canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n*
        sourceCriticalGapQuotient hp hp1 ψ n := by
  unfold sourceActionCriticalCoordinate sourceStandardRootMidpoint sourceStandardRootHalfGap
  rw [H.criticalOffsets.exact_offset ψ hψ n,sourcePeriodicGapDisplacement_apply]
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · rw [hg]
    simp
  · field_simp
    ring

/-- Equation (2.19) with its literal factor four, weight and complex gap parametrization. -/
theorem SourceEquation2_18Data.normalizedAction_eq_chi_gapIntegral
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W) (hWc : IsPreconnected W)
    (hR : realTypeSourceLocus p ⊆ W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hgap : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    4*sourceIndexedAction hp hp1 n ψ /
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 =
      (2/(Real.pi:ℂ)) * ∫ t in (-1:ℝ)..1,
        (sourceActionCriticalCoordinate hp hp1 n ψ-(t:ℂ))^2/(Real.sqrt (1-t^2):ℂ)*
          sourceActionChi hp hp1 n ψ
            (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ)) := by
  rw [H.action_eq_chi_gapIntegral hW hWc hR ψ hψ n]
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
      2*sourceStandardRootHalfGap hp hp1 ψ n := by unfold sourceStandardRootHalfGap; ring
  have hd : sourceStandardRootHalfGap hp hp1 ψ n ≠ 0 := div_ne_zero hgap (by norm_num)
  rw [hg]
  calc
    _ = (2/(Real.pi:ℂ)) *
        ((sourceStandardRootHalfGap hp hp1 ψ n)^2)⁻¹ * ∫ t in (-1:ℝ)..1,
          (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
            sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))^2 /
            (Real.sqrt (1-t^2):ℂ)*sourceActionChi hp hp1 n ψ
              (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ)) := by ring
    _ = _ := by
      rw [mul_assoc,← intervalIntegral.integral_const_mul]
      congr 1
      apply intervalIntegral.integral_congr
      intro t _
      dsimp only [sourceActionCriticalCoordinate]
      field_simp

end NLS.ZakharovShabat
