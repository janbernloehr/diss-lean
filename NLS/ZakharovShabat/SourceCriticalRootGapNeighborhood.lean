import NLS.ZakharovShabat.SourceCriticalRootRatioGapSideLimits
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A controlled neighborhood of the selected periodic gap

For a real-type source, every point of the selected closed gap avoids
all other gap segments. Compactness supplies a uniform transverse
neighborhood that still avoids them. The omitted root product is
nonzero there, so its reciprocal has a uniform bound. This isolates
the only possible singular behavior of the critical-root quotient to
the selected standard root itself.
-/

noncomputable section
open Set Metric Complex
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- At a real-type source, the domain of the omitted product is open
in the spectral variable. -/
theorem isOpen_sourceStandardRootOmittedDomain_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    IsOpen (sourceStandardRootOmittedDomain hp hp1 ψ n) := by
  obtain ⟨W,_,_,hWreal,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have heq : sourceStandardRootOmittedDomain hp hp1 ψ n =
      (fun z : ℂ => (z,ψ)) ⁻¹'
        sourceStandardRootOmittedJointDomain hp hp1 W n := by
    ext z
    change (∀ m, m ≠ n → z ∉ sourcePeriodicSegment hp hp1 ψ m) ↔
      ψ ∈ W ∧ (∀ m, m ≠ n → z ∉ sourcePeriodicSegment hp hp1 ψ m)
    exact ⟨fun hz => ⟨hψ,hz⟩, And.right⟩
  rw [heq]
  exact (hdata n).1.preimage (continuous_id.prodMk continuous_const)

/-- The selected closed gap lies in the domain where all other
standard-root factors remain analytic and nonzero. -/
theorem sourceStandardRootGapSegment_subset_omittedDomain_of_realType
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    standardRootGapSegment
      (sourceStandardRootMidpoint hp hp1 ψ n)
      (sourceStandardRootHalfGap hp hp1 ψ n) ⊆
      sourceStandardRootOmittedDomain hp hp1 ψ n := by
  obtain ⟨W,_,_,hWreal,hpoint⟩ :=
    exists_global_source_gapPoint_mem_omittedDomain hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  intro z hz
  obtain ⟨t,ht,rfl⟩ := hz
  change sourceCanonicalRootGapPoint hp hp1 ψ n t ∈
    sourceStandardRootOmittedDomain hp hp1 ψ n
  exact hpoint ψ hψ n t ht.1 ht.2

/-- A uniform closed thickening of the selected gap avoids all other
gaps, and the inverse omitted product stays bounded there. -/
theorem exists_sourceCriticalRootGap_thickening_inverseOmitted_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      cthickening ε
        (standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ n ∧
      ∀ z ∈ cthickening ε
        (standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)),
        ‖(sourceStandardRootOmittedProduct hp hp1 n ψ z)⁻¹‖ ≤ M := by
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  let D := sourceStandardRootOmittedDomain hp hp1 ψ n
  let P := sourceStandardRootOmittedProduct hp hp1 n ψ
  have hS : IsCompact S := standardRootGapSegment_compact _ _
  have hDopen : IsOpen D :=
    isOpen_sourceStandardRootOmittedDomain_of_realType hp hp1 ψ hreal n
  have hSD : S ⊆ D :=
    sourceStandardRootGapSegment_subset_omittedDomain_of_realType
      hp hp1 ψ hreal n
  obtain ⟨ε,hε,hthick⟩ := hS.exists_cthickening_subset_open hDopen hSD
  have hK : IsCompact (cthickening ε S) := hS.cthickening
  obtain ⟨W,_,_,hWreal,hdata⟩ :=
    exists_global_source_analytic_omittedJointProduct hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have hPanalytic : AnalyticOnNhd ℂ P D :=
    sourceStandardRootOmittedProduct_analyticOnNhd_spectral
      hp hp1 n W (hdata n).2.1 ψ hψ
  have hPinv : ContinuousOn (fun z => (P z)⁻¹) (cthickening ε S) := by
    intro z hz
    have hzD : z ∈ D := hthick hz
    have hPne : P z ≠ 0 :=
      sourceStandardRootOmittedProduct_ne_zero hp hp1 ψ z n hzD
    exact ((hPanalytic z hzD).continuousAt.inv₀ hPne).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hPinv
  refine ⟨ε,max C 0+1,hε,by positivity,hthick,?_⟩
  intro z hz
  exact (hC z hz).trans (by linarith [le_max_left C 0])

/-- On a uniform transverse neighborhood of the selected gap, the
regular critical-root numerator has a finite bound. -/
theorem exists_sourceCriticalRootGap_thickening_regularNumerator_bound
    (hp : p ≠ ⊤) (hp1 : 1 < p)
    (ψ : CoeffPair p) (hreal : IsRealType (CoeffPair.toMax p ψ))
    (n : ℤ) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      cthickening ε
        (standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)) ⊆
        sourceStandardRootOmittedDomain hp hp1 ψ n ∧
      ∀ z ∈ cthickening ε
        (standardRootGapSegment
          (sourceStandardRootMidpoint hp hp1 ψ n)
          (sourceStandardRootHalfGap hp hp1 ψ n)),
        ‖sourceCriticalRootGapNumerator hp hp1 ψ n z‖ ≤ M := by
  let S := standardRootGapSegment
    (sourceStandardRootMidpoint hp hp1 ψ n)
    (sourceStandardRootHalfGap hp hp1 ψ n)
  let D := sourceStandardRootOmittedDomain hp hp1 ψ n
  let F := sourceCriticalRootGapNumerator hp hp1 ψ n
  obtain ⟨ε,_,hε,_,hKdom,_⟩ :=
    exists_sourceCriticalRootGap_thickening_inverseOmitted_bound
      hp hp1 ψ hreal n
  have hK : IsCompact (cthickening ε S) :=
    (standardRootGapSegment_compact _ _).cthickening
  obtain ⟨W,_,hWreal,hext⟩ :=
    exists_global_sourceCriticalRootRatioExtension_analytic hp hp1
  have hψ : ψ ∈ W := hWreal hreal
  have hFcont : ContinuousOn F (cthickening ε S) := by
    intro z hz
    have hzD : z ∈ D := hKdom hz
    have hE : ContinuousAt (sourceCriticalRootRatioExtension hp hp1 n ψ) z :=
      (hext ψ hψ n z hzD).continuousAt
    change ContinuousWithinAt
      (fun w : ℂ =>
        (canonicalCriticalPoints hp hp1 (periodOnePotential ψ)
          (periodOnePotential_mem ψ) n-w) *
          sourceCriticalRootRatioExtension hp hp1 n ψ w)
      (cthickening ε S) z
    exact ((continuousAt_const.sub continuousAt_id).mul hE).continuousWithinAt
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hFcont
  refine ⟨ε,max C 0+1,hε,by positivity,hKdom,?_⟩
  intro z hz
  exact (hC z hz).trans (by linarith [le_max_left C 0])

end NLS.ZakharovShabat
