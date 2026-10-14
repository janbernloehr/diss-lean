import NLS.ZakharovShabat.SourceIndexedActionCommonCharts
import NLS.ZakharovShabat.SourceNormalizedActionRootAnalytic
import NLS.ZakharovShabat.SourceNormalizedActionOnePlusDecomposition

/-!
# Normalized indexed actions on one local source neighborhood

The chart bridge identifies the actual indexed actions with the existing
analytic factors. A finite intersection preserves one neighborhood for
all indices, positive lower bounds and the literal two sequence remainders.
The one-plus summands are fixed before any exponent is chosen.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Uniform bounds on one source set, with genuine ℓ^(1+) summands. -/
structure SourceNormalizedActionUniformBounds (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) : Prop where
  positive : ∃ c : ℝ, 0 < c ∧ ∀ ψ ∈ V, ∀ n : ℤ,
    c ≤ (sourceNormalizedActionComplexExtension hp hp1 n ψ).re
  asymptotics :
    ∃ GA GR : CoeffPair p → Coeff (ENNReal.ofReal (p.toReal/2)),
    ∃ BA BR : CoeffPair p → CoeffOnePlus,
      (∀ ψ ∈ V, ∀ n : ℤ,
        GA ψ n + (BA ψ).1 n = 4*sourceNormalizedActionComplexExtension hp hp1 n ψ-1 ∧
        GR ψ n + (BR ψ).1 n = sourceNormalizedActionRoot hp hp1 n ψ-1) ∧
      ContinuousOn BA V ∧ ContinuousOn BR V ∧
      (∃ Ma Mr : ℝ, ∀ ψ ∈ V, ‖GA ψ‖ ≤ Ma ∧ ‖GR ψ‖ ≤ Mr) ∧
      ∀ (q : ℝ≥0∞) (hq1 : 1 < q) (hq : q ≠ ⊤),
        ∃ La Lr : ℝ, ∀ ψ ∈ V,
          ‖CoeffOnePlus.toCoeff q hq1 hq (BA ψ)‖ ≤ La ∧
          ‖CoeffOnePlus.toCoeff q hq1 hq (BR ψ)‖ ≤ Lr

/-- Restriction keeps the same constants and the same sequence summands. -/
theorem SourceNormalizedActionUniformBounds.mono
    {hp : p ≠ ⊤} {hp1 : 1 < p} {U V : Set (CoeffPair p)}
    (H : SourceNormalizedActionUniformBounds hp hp1 V) (hUV : U ⊆ V) :
    SourceNormalizedActionUniformBounds hp hp1 U := by
  obtain ⟨c,hc,hpos⟩ := H.positive
  obtain ⟨GA,GR,BA,BR,he,hBA,hBR,⟨Ma,Mr,hb⟩,hq⟩ := H.asymptotics
  refine ⟨⟨c,hc,fun ψ hψ n => hpos ψ (hUV hψ) n⟩,
    GA,GR,BA,BR,(fun ψ hψ n => he ψ (hUV hψ) n),hBA.mono hUV,hBR.mono hUV,
    ⟨Ma,Mr,fun ψ hψ => hb ψ (hUV hψ)⟩,?_⟩
  intro q hq1 hqt
  obtain ⟨La,Lr,hbound⟩ := hq q hq1 hqt
  exact ⟨La,Lr,fun ψ hψ => hbound ψ (hUV hψ)⟩

/-- All local conclusions refer to the actual indexed actions. -/
structure SourceNormalizedIndexedActionLocalData (hp : p ≠ ⊤) (hp1 : 1 < p)
    (V : Set (CoeffPair p)) : Prop where
  analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedActionComplexExtension hp hp1 n) V
  root_analytic : ∀ n : ℤ, AnalyticOnNhd ℂ (sourceNormalizedActionRoot hp hp1 n) V
  factorization : ∀ ψ ∈ V, ∀ n : ℤ, sourceIndexedAction hp hp1 n ψ =
    (canonicalPeriodicGap hp hp1 (periodOnePotential ψ) (periodOnePotential_mem ψ) n)^2 *
      sourceNormalizedActionComplexExtension hp hp1 n ψ
  agreement : ∀ ψ ∈ V, ∀ n : ℤ, ψ ∈ sourceComplexActionDomain hp hp1 n ∧
    sourceIndexedAction hp hp1 n ψ = sourceComplexAction hp hp1 n ψ
  uniform : SourceNormalizedActionUniformBounds hp hp1 V

/-- The analytic normalization and both asymptotics hold simultaneously near
each real source, on a neighborhood contained in the retained domain W. -/
theorem SourceSection11ContourData.normalizedActions_near_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (H : SourceSection11ContourData hp hp1 W)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφW : φ ∈ W) :
    ∃ V : Set (CoeffPair p), IsOpen V ∧ φ ∈ V ∧ V ⊆ W ∧
      SourceNormalizedIndexedActionLocalData hp hp1 V := by
  obtain ⟨U,hU,_,hφU,hUW,he⟩ :=
    H.indexedAction_eq_complexAction_allIndices_near_real φ hφ hφW
  obtain ⟨Va,hVa,hφa,ha,hfactor⟩ :=
    exists_local_sourceNormalizedAction_allIndices_analytic_factor hp hp1 φ hφ
  obtain ⟨Vr,hVr,hφr,hr,_⟩ :=
    exists_local_sourceNormalizedActionRoot_allIndices_analytic hp hp1 φ hφ
  have hhalf : ENNReal.ofReal (p.toReal/2) ≤ p := by
    rw [ENNReal.ofReal_le_iff_le_toReal hp]
    linarith [ENNReal.toReal_nonneg (a := p)]
  obtain ⟨Vp,hVp,hφp,c,hc,hpos⟩ :=
    exists_local_sourceNormalizedActionComplexExtension_uniform_re_pos
      (q := p) hp hp1 hp1 hp hhalf φ hφ
  obtain ⟨Vb,hVb,hφb,GA,GR,BA,BR,hcoords,hBA,hBR,⟨Ma,Mr,hbounds⟩,hq⟩ :=
    exists_local_sourceNormalizedAction_onePlus_decomposition hp hp1 φ hφ
  let V := U ∩ (Va ∩ (Vr ∩ (Vp ∩ Vb)))
  have hV : IsOpen V := hU.inter (hVa.inter (hVr.inter (hVp.inter hVb)))
  refine ⟨V,hV,⟨hφU,hφa,hφr,hφp,hφb⟩,(fun ψ hψ => hUW hψ.1),?_,?_,?_,?_,?_⟩
  · exact fun n ψ hψ => ha n ψ hψ.2.1
  · exact fun n ψ hψ => hr n ψ hψ.2.2.1
  · intro ψ hψ n
    rw [(he ψ hψ.1 n).2]
    simpa only [sourcePeriodicGapDisplacement_apply] using! hfactor ψ hψ.2.1 n
  · exact fun ψ hψ n => he ψ hψ.1 n
  · refine ⟨⟨c/4,by positivity,?_⟩,GA,GR,BA,BR,?_,
      hBA.mono (fun ψ hψ => hψ.2.2.2.2),hBR.mono (fun ψ hψ => hψ.2.2.2.2),
      ⟨Ma,Mr,fun ψ hψ => hbounds ψ hψ.2.2.2.2⟩,?_⟩
    · intro ψ hψ n
      have hh := hpos ψ hψ.2.2.2.1 n
      simp [Complex.mul_re] at hh
      linarith
    · exact fun ψ hψ n => hcoords ψ hψ.2.2.2.2 n
    · intro q hq1 hqt
      obtain ⟨La,Lr,hb⟩ := hq q hq1 hqt
      exact ⟨La,Lr,fun ψ hψ => hb ψ hψ.2.2.2.2⟩

end NLS.ZakharovShabat
