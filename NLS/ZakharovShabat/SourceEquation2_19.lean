import NLS.ZakharovShabat.SourceActionChiGapIntegral
import NLS.ZakharovShabat.SourceNormalizedIndexedActionCommon
import NLS.ZakharovShabat.SourceTheorem11_2

/-!
# Equation (2.19) and the collapsed-gap extension on the original W

The literal weighted integral, its normalized version and the collapsed
limit all use the actual indexed actions and canonical gaps. Analyticity
of the filled quotient holds on the entire preceding source domain.
-/

noncomputable section
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The source's gap-integral formulas and analytic extension, retaining W. -/
structure SourceEquation2_19Data (hp : p ≠ ⊤) (hp1 : 1 < p) (W : Set (CoeffPair p)) : Prop where
  previous : SourceEquation2_18Data hp hp1 W
  action_integral : ∀ ψ ∈ W, ∀ n : ℤ,
    sourceIndexedAction hp hp1 n ψ = (2/(Real.pi:ℂ)) * ∫ t in (-1:ℝ)..1,
      (canonicalCriticalPoints hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n-
        sourceStandardRootMidpoint hp hp1 ψ n-sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))^2 /
        (Real.sqrt (1-t^2):ℂ)*sourceActionChi hp hp1 n ψ
          (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))
  normalized_integral : ∀ ψ ∈ W, ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n ≠ 0 →
    4*sourceIndexedAction hp hp1 n ψ /
        (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 =
      (2/(Real.pi:ℂ)) * ∫ t in (-1:ℝ)..1,
        (sourceActionCriticalCoordinate hp hp1 n ψ-(t:ℂ))^2/(Real.sqrt (1-t^2):ℂ)*
          sourceActionChi hp hp1 n ψ
            (sourceStandardRootMidpoint hp hp1 ψ n+sourceStandardRootHalfGap hp hp1 ψ n*(t:ℂ))
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedIndexedAction hp hp1 n) W
  factorization : ∀ ψ ∈ W, ∀ n : ℤ,
    sourceIndexedAction hp hp1 n ψ =
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2*
        sourceNormalizedIndexedAction hp hp1 n ψ
  collapsed_limit : ∀ φ ∈ W, ∀ n : ℤ,
    canonicalPeriodicGap hp hp1 (periodOnePotential φ) (periodOnePotential_mem φ) n = 0 →
    Tendsto (fun ψ : CoeffPair p => 4*sourceIndexedAction hp hp1 n ψ /
      (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2)
      (𝓝[W \ {ψ | canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0}] φ)
      (𝓝 (sourceActionChi hp hp1 n φ (sourceStandardRootMidpoint hp hp1 φ n)))

/-- Both integral formulas and the extension hold on the original connected domain. -/
theorem SourceEquation2_18Data.gapFormulas
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_18Data hp hp1 W) (hW : IsOpen W) (hWc : IsPreconnected W)
    (hR : realTypeSourceLocus p ⊆ W) : SourceEquation2_19Data hp hp1 W :=
  ⟨H,H.action_eq_chi_gapIntegral hW hWc hR,H.normalizedAction_eq_chi_gapIntegral hW hWc hR,
    H.normalizedIndexedAction_analytic,H.indexedAction_eq_gap_sq_mul_normalized,H.normalizedAction_tendsto_collapsed⟩

/-- The source's midpoint value χ_n(τ_n) is analytic on the entire original W. -/
theorem SourceEquation2_19Data.midpointChi_analytic
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W) (n : ℤ) :
    AnalyticOnNhd ℂ (fun ψ => sourceActionChi hp hp1 n ψ (sourceStandardRootMidpoint hp hp1 ψ n)) W := by
  intro ψ hψ
  have hm := H.previous.criticalOffsets.previous.previous.previous.roots.roots.symmetric.midpoint n ψ hψ
  exact (H.previous.joint n (sourceStandardRootMidpoint hp hp1 ψ n,ψ)
    ⟨hψ,H.previous.segment_subset_omitted ψ hψ n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n)⟩).comp
      (f := fun χ : CoeffPair p => (sourceStandardRootMidpoint hp hp1 χ n,χ)) (hm.prod analyticAt_id)

/-- Compatibility with the normalized action already used in Theorem 11.2. -/
theorem SourceEquation2_19Data.normalized_eq_theorem11_2
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W₀) (Hn : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ) :
    sourceNormalizedIndexedAction hp hp1 n ψ = sourceNormalizedActionComplexExtension hp hp1 n ψ := by
  by_cases hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0
  · have hd : sourcePeriodicGapDisplacement hp hp1 ψ n = 0 := by
      simpa only [sourcePeriodicGapDisplacement_apply] using hg
    rw [sourceNormalizedIndexedAction_eq_collapsed hp hp1 n ψ hg]
    simp only [sourceNormalizedActionComplexExtension,sourceNormalizedActionRealExtension,if_pos hd,
      sourceNormalizedActionCollapsedCandidate]
    rw [sourceCriticalRootRatioExtension_eq_neg_I_chi hp hp1 ψ n _
      (H.previous.segment_subset_omitted ψ (Hn.subset hψ) n (sourcePeriodicMidpoint_mem_segment hp hp1 ψ n))]
    rw [← mul_assoc,mul_neg,Complex.I_mul_I]
    ring
  · rw [sourceNormalizedIndexedAction_eq_quotient hp hp1 n ψ hg,Hn.normalized_eq_quotient ψ hψ n hg]

/-- At collapse the established principal root squares to χ_n(τ_n). -/
theorem SourceEquation2_19Data.normalizedRoot_sq_eq_chi_of_gap_zero
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W₀ W : Set (CoeffPair p)}
    (H : SourceEquation2_19Data hp hp1 W₀) (Hn : SourceTheorem11_2Data hp hp1 W₀ W)
    (ψ : CoeffPair p) (hψ : ψ ∈ W) (n : ℤ)
    (hg : canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n = 0) :
    (sourceNormalizedActionRoot hp hp1 n ψ)^2 =
      sourceActionChi hp hp1 n ψ (sourceStandardRootMidpoint hp hp1 ψ n) := by
  rw [Hn.root_sq ψ n,← H.normalized_eq_theorem11_2 Hn ψ hψ n,
    sourceNormalizedIndexedAction_eq_collapsed hp hp1 n ψ hg]
  ring

/-- The filled indexed quotient has the expected nonzero free normalization. -/
theorem sourceNormalizedIndexedAction_zero_source (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) :
    sourceNormalizedIndexedAction hp hp1 n (0 : CoeffPair p) = 1/4 := by
  obtain ⟨W,_,_,hr,H⟩ := sourceEquation2_18 hp hp1
  have h0 : (0 : CoeffPair p) ∈ W := hr (by simp [realTypeSourceLocus])
  have hg : canonicalPeriodicGap hp hp1 (periodOnePotential (0 : CoeffPair p)) (periodOnePotential_mem 0) n = 0 := by
    simpa only [map_zero] using canonicalPeriodicGap_zero hp hp1 n
  rw [sourceNormalizedIndexedAction_eq_collapsed hp hp1 n 0 hg,
    sourceActionChi_zero_source hp hp1 n _
      (H.segment_subset_omitted 0 h0 n (sourcePeriodicMidpoint_mem_segment hp hp1 0 n))]

/-- Equation (2.19), the collapsed limit and analytic extension for every finite p>1. -/
theorem sourceEquation2_19 (hp : p ≠ ⊤) (hp1 : 1 < p) :
    ∃ W : Set (CoeffPair p), IsOpen W ∧ IsConnected W ∧ realTypeSourceLocus p ⊆ W ∧
      SourceEquation2_19Data hp hp1 W := by
  obtain ⟨W,ho,hc,hr,H⟩ := sourceEquation2_18 hp hp1
  exact ⟨W,ho,hc,hr,H.gapFormulas ho hc.isPreconnected hr⟩

end NLS.ZakharovShabat
