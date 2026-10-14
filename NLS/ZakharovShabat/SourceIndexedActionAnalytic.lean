import NLS.ZakharovShabat.SourceIndexedAction
import NLS.ZakharovShabat.SourceSection11Contours
import NLS.ZakharovShabat.SourceRealActionRealCenteredCircle
import NLS.ZakharovShabat.SourceComplexActionProperties
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# The indexed action on the unchanged common source domain

Local simultaneous circles represent one indexed function throughout W.
It agrees with the existing real action everywhere on the real locus and
with the previous glued complex action near each real source. The two
complex functions also agree on any connected overlap containing such a
source. No containment of W in the older chart union is assumed.
-/

noncomputable section
open Set Metric Filter Topology Complex NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Each indexed action is analytic on the entire retained W. -/
theorem SourceSection11ContourData.analytic_indexedAction
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSection11ContourData hp hp1 W) (hW : IsOpen W) (n : ℤ) :
    AnalyticOnNhd ℂ (sourceIndexedAction hp hp1 n) W := by
  apply analyticOnNhd_of_complexDifferentiableOn _ W hW
  intro ψ hψ
  obtain ⟨U,hU,_,hψU,_,D,c,hD,C,ha⟩ := h.neighborhoods ψ hψ
  have he : sourceIndexedAction hp hp1 n =ᶠ[𝓝 ψ]
      (fun χ => sourceActionCircle hp hp1 χ (C.center n : ℂ) (C.radius n)) := by
    filter_upwards [hU.mem_nhds hψU] with χ hχ
    exact C.indexedAction_eq_circle hD χ hχ n
  exact (((ha n).2 ψ hψU).differentiableAt.congr_of_eventuallyEq he).differentiableWithinAt

/-- On every real source, the circle-independent action is the existing
indexed real action, including the central and collapsed cases. -/
theorem sourceIndexedAction_eq_sourceRealAction
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    sourceIndexedAction hp hp1 n φ = sourceRealAction hp hp1 φ hφ n := by
  obtain ⟨N,ε,_,_,V,_,_,hφV,c,hD⟩ :=
    exists_local_source_quantitative_isolating_discs hp hp1 φ hφ
  obtain ⟨a,r,hr,he⟩ := hD.discs n
  let D := hD.periodCircle φ hφV n a r hr he
  rw [sourceIndexedAction_eq_circle D]
  exact (sourceRealAction_eq_realCentered_enclosingCircle hp hp1 φ hφ n
    (D.center : ℂ) D.radius (by simp) D.radius_pos D.gap D.closedBall_subset_omittedDomain).symm

/-- Real nonnegativity and the exact zero-gap criterion are preserved. -/
theorem sourceIndexedAction_nonneg_and_eq_zero_iff_gap_zero
    (hp : p ≠ ⊤) (hp1 : 1 < p) (n : ℤ) (φ : CoeffPair p)
    (hφ : IsRealType (CoeffPair.toMax p φ)) :
    0 ≤ (sourceIndexedAction hp hp1 n φ).re ∧ (sourceIndexedAction hp hp1 n φ).im = 0 ∧
      (sourceIndexedAction hp hp1 n φ = 0 ↔ sourcePeriodicGapDisplacement hp hp1 φ n = 0) := by
  rw [sourceIndexedAction_eq_sourceRealAction hp hp1 n φ hφ]
  exact sourceRealAction_nonneg_and_eq_zero_iff_gap_zero hp hp1 φ hφ n

/-- The new action and the earlier complex chart construction have the
same complex germ at every real source in W. -/
theorem SourceSection11ContourData.indexedAction_eq_complexAction_near_real
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSection11ContourData hp hp1 W) (hW : IsOpen W) (n : ℤ)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφW : φ ∈ W) :
    ∃ U : Set (CoeffPair p), IsOpen U ∧ φ ∈ U ∧
      U ⊆ W ∩ sourceComplexActionDomain hp hp1 n ∧
        EqOn (sourceIndexedAction hp hp1 n) (sourceComplexAction hp hp1 n) U := by
  apply exists_local_eqOn_of_eqOn_realType hp φ hφ W (sourceComplexActionDomain hp hp1 n)
    hW (isOpen_sourceComplexActionDomain hp hp1 n) hφW
    (realTypeSourceLocus_subset_sourceComplexActionDomain hp hp1 n hφ)
    (sourceIndexedAction hp hp1 n) (sourceComplexAction hp hp1 n)
    (h.analytic_indexedAction hW n).differentiableOn (sourceComplexAction_differentiableOn hp hp1 n)
  intro ψ _ hψ
  exact (sourceIndexedAction_eq_sourceRealAction hp hp1 n ψ hψ).trans
    (sourceComplexAction_eq_sourceRealAction hp hp1 n ψ hψ).symm

/-- Agreement propagates over every connected overlap containing a real
source. No claim about unrelated overlap components is needed. -/
theorem SourceSection11ContourData.indexedAction_eq_complexAction_on_overlap
    {hp : p ≠ ⊤} {hp1 : 1 < p} {W : Set (CoeffPair p)}
    (h : SourceSection11ContourData hp hp1 W) (hW : IsOpen W) (n : ℤ)
    (U : Set (CoeffPair p)) (hUc : IsPreconnected U)
    (hUW : U ⊆ W) (hUD : U ⊆ sourceComplexActionDomain hp hp1 n)
    (φ : CoeffPair p) (hφ : IsRealType (CoeffPair.toMax p φ)) (hφU : φ ∈ U) :
    EqOn (sourceIndexedAction hp hp1 n) (sourceComplexAction hp hp1 n) U := by
  have hA := (h.analytic_indexedAction hW n).mono hUW
  have hB := (analyticOnNhd_of_complexDifferentiableOn _ _
    (isOpen_sourceComplexActionDomain hp hp1 n) (sourceComplexAction_differentiableOn hp hp1 n)).mono hUD
  obtain ⟨V,hV,hφV,_,he⟩ := h.indexedAction_eq_complexAction_near_real hW n φ hφ (hUW hφU)
  exact hA.eqOn_of_preconnected_of_eventuallyEq hB hUc hφU
    (Filter.mem_of_superset (hV.mem_nhds hφV) he)

end NLS.ZakharovShabat
