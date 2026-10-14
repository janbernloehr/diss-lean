import NLS.ZakharovShabat.SourceNormalizedActionCommonKernel
import NLS.ZakharovShabat.SourceNormalizedActionCollapsedCircleValue

/-!
# Normalized indexed actions on the entire original domain

Fill the actual quotient by χ_n at the midpoint divided by four at a
collapsed gap. Local agreement with the rationalized circle candidate
proves analyticity on the original W, including non-real collapsed gaps.
The previous complex-action chart domain is not assumed to contain W.
-/

noncomputable section
open Set Metric Complex Filter Topology NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The actual indexed quotient with the source's stated collapsed value. -/
def sourceNormalizedIndexedAction (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (ψ : CoeffPair p) : ℂ := by
  classical
  exact if canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0 then
    sourceActionChi hp hp1 n ψ (sourceStandardRootMidpoint hp hp1 ψ n)/4
  else sourceIndexedAction hp hp1 n ψ /
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2

/-- On the open-gap set the filled function is the literal indexed quotient. -/
theorem sourceNormalizedIndexedAction_eq_quotient (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0) :
    sourceNormalizedIndexedAction hp hp1 n ψ = sourceIndexedAction hp hp1 n ψ /
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 := by
  simp only [sourceNormalizedIndexedAction,if_neg hg]

/-- The collapsed value is one quarter of the literal deleted product at the midpoint. -/
theorem sourceNormalizedIndexedAction_eq_collapsed (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ)
    (ψ : CoeffPair p)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    sourceNormalizedIndexedAction hp hp1 n ψ =
      sourceActionChi hp hp1 n ψ (sourceStandardRootMidpoint hp hp1 ψ n)/4 := by
  simp only [sourceNormalizedIndexedAction,if_pos hg]

/-- Every original local contour computes the filled normalized indexed action. -/
theorem SourceActionContourFamily.normalizedIndexedAction_eq_circleCandidate
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W V : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hVW : V ⊆ W)
    {D : ℤ → Set ℂ} {c : ℝ} (hD : SourceIsolatingNeighborhoods hp hp1 V D c)
    (C : SourceActionContourFamily hp hp1 V D) (ψ : CoeffPair p) (hψ : ψ ∈ V) (n : ℤ) :
    sourceNormalizedIndexedAction hp hp1 n ψ =
      sourceNormalizedActionCircleCandidate hp hp1 n (C.center n : ℂ) (C.radius n) ψ := by
  let P := C.periodCircle hD ψ hψ n
  have hE : AnalyticOnNhd ℂ (sourceCriticalRootRatioExtension hp hp1 n ψ)
      (closedBall (C.center n : ℂ) (C.radius n)) :=
    (H.criticalOffsets.previous.previous.previous.criticalRatioExtension ψ (hVW hψ) n).mono
      P.closedBall_subset_omittedDomain
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · rw [sourceNormalizedIndexedAction_eq_collapsed hp hp1 n ψ hg,
      sourceNormalizedActionCircleCandidate_eq_collapsedCandidate_of_gap_zero hp hp1 ψ n
        (C.center n : ℂ) (C.radius n) P.radius_pos
        (by simpa only [sourcePeriodicGapDisplacement_apply] using hg) P.gap hE]
    unfold sourceNormalizedActionCollapsedCandidate
    rw [sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n _
      (H.segment_subset_omitted ψ (hVW hψ) n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))]
    rw [← mul_assoc,mul_neg,Complex.I_mul_I]
    ring
  · have hzero := H.previous.previous.previous.previous.previous.zero ψ (hVW hψ) n P
    have hoffset : canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        canonicalPeriodicMidpoint hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n =
        (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
          canonicalCriticalGapQuotient hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n := by
      have he := H.criticalOffsets.exact_offset ψ (hVW hψ) n
      rw [sourceCriticalGapQuotient_apply] at he
      linear_combination he
    have hf := sourceActionCircle_eq_squaredGap_mul_kernel hp hp1 ψ n _ _ _ P.radius_pos.le
      P.sphere_subset_rootDomain (fun z hz => P.sphere_subset_rootDomain hz n) hzero hE hoffset
    change sourceActionCircle hp hp1 ψ (C.center n : ℂ) (C.radius n) =
      (sourcePeriodicGapDisplacement hp hp1 ψ n)^2*
        sourceNormalizedActionCircleCandidate hp hp1 n (C.center n : ℂ) (C.radius n) ψ at hf
    rw [sourceNormalizedIndexedAction_eq_quotient hp hp1 n ψ hg,
      C.indexedAction_eq_circle hD ψ hψ n,hf,sourcePeriodicGapDisplacement_apply]
    field_simp

/-- Analyticity of the filled quotient throughout the original complex source domain. -/
theorem SourceEquation2_18Data.normalizedIndexedAction_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceNormalizedIndexedAction hp hp1 n) W := by
  intro φ hφ
  obtain ⟨V,hV,_,hφV,hVW,D,c,hD,C,_⟩ := H.previous.previous.previous.neighborhoods φ hφ
  have ha := C.analytic_normalizedActionCircleCandidate H hV hVW hD n φ hφV
  apply ha.congr
  filter_upwards [hV.mem_nhds hφV] with ψ hψ
  exact (C.normalizedIndexedAction_eq_circleCandidate H hVW hD ψ hψ n).symm

/-- The exact action factorization includes every collapsed complex gap on W. -/
theorem SourceEquation2_18Data.indexedAction_eq_gap_sq_mul_normalized
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceIndexedAction hp hp1 n ψ =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2*
        sourceNormalizedIndexedAction hp hp1 n ψ := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · rw [H.previous.collapsed ψ hψ n hg,hg]
    simp
  · rw [sourceNormalizedIndexedAction_eq_quotient hp hp1 n ψ hg]
    field_simp

/-- The source's collapsed limit holds along arbitrary complex approaches within W. -/
theorem SourceEquation2_18Data.normalizedAction_tendsto_collapsed
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (φ : CoeffPair p) (hφ : φ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0) :
    Tendsto (fun ψ : CoeffPair p => 4*sourceIndexedAction hp hp1 n ψ /
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2)
      (𝓝[W \ {ψ | canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0}] φ)
      (𝓝 (sourceActionChi hp hp1 n φ (sourceStandardRootMidpoint hp hp1 φ n))) := by
  have ht := ((H.normalizedIndexedAction_analytic n φ hφ).continuousAt.const_mul (4:ℂ)).tendsto.mono_left
    (nhdsWithin_le_nhds (s := W \ {ψ | canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0}))
  rw [sourceNormalizedIndexedAction_eq_collapsed hp hp1 n φ hg] at ht
  have hval (z : ℂ) : 4*(z/4) = z := by ring
  rw [hval] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with ψ hψ
  rw [sourceNormalizedIndexedAction_eq_quotient hp hp1 n ψ hψ.2]
  ring

end NLS.ZakharovShabat
