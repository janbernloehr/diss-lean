import NLS.SequenceSpaces.NonnegativeAnalyticDensity
import NLS.FunctionalAnalysis.CompactAnalyticDeterminant

/-! # Fredholm density on the nonnegative sequence cone

The parameter domain carries its relative topology. Analytic extensions are
local and may vary from point to point; compactness is required only at real
nonnegative parameters, never throughout an ambient complex neighborhood.
-/
noncomputable section
open Set Filter Topology Metric
open scoped ENNReal
namespace NLS.Coeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Local holomorphic extensions of a map on the nonnegative cone. On a
relatively open domain the values outside that domain are immaterial. -/
def HasLocalAnalyticExtensions (f : nonnegativeLocus p → F)
    (U : Set (nonnegativeLocus p)) : Prop :=
  ∀ x ∈ U, ∃ g : Coeff p → F, AnalyticAt ℂ g x.val ∧
    f =ᶠ[𝓝 x] (fun y => g y.val)

/-- A locally extendible cone map is relatively continuous. -/
theorem HasLocalAnalyticExtensions.continuousOn
    {f : nonnegativeLocus p → F} {U : Set (nonnegativeLocus p)}
    (hf : HasLocalAnalyticExtensions f U) : ContinuousOn f U := by
  intro x hx
  obtain ⟨g,hg,he⟩ := hf x hx
  exact ((hg.continuousAt.comp continuous_subtype_val.continuousAt).congr_of_eventuallyEq he).continuousWithinAt

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- The relative form of analytic Fredholm density needed in Proposition I.4.
The source may contain any boundary points of the nonnegative cone. -/
theorem open_dense_isUnit_of_nonnegative_analytic_compact_shift
    (hp : p ≠ ⊤) {A : nonnegativeLocus p → E →L[ℂ] E}
    {U : Set (nonnegativeLocus p)} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hA : HasLocalAnalyticExtensions A U) {c : ℂ} (hc : c ≠ 0)
    (hcompact : ∀ x ∈ U, IsCompactOperator (A x - c • 1 : E →L[ℂ] E))
    (hstart : ∃ x ∈ U, IsUnit (A x)) :
    IsOpen {x ∈ U | IsUnit (A x)} ∧ U ⊆ closure {x ∈ U | IsUnit (A x)} := by
  have hS : IsOpen {x ∈ U | IsUnit (A x)} :=
    hA.continuousOn.isOpen_inter_preimage hU Units.isOpen
  refine ⟨hS, subset_closure_of_nonnegative_local_analytic_nonvanishing hp hconn hS ?_ ?_⟩
  · obtain ⟨x,hx,hu⟩ := hstart
    exact ⟨x,hx,hx,hu⟩
  · intro x hx
    obtain ⟨B,hB,he⟩ := hA x hx
    obtain ⟨V,hV,hxV,d,hd,hcrit⟩ := CompactSpectrum.exists_local_analytic_determinant
      hB hc (by rw [← he.eq_of_nhds]; exact hcompact x hx)
    obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp
      (Filter.inter_mem (hU.mem_nhds hx)
        (Filter.inter_mem ((hV.preimage continuous_subtype_val).mem_nhds hxV) he))
    obtain ⟨s,hs,hsball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hxV)
    refine ⟨min r s,lt_min hr hs,d,hd.mono (fun y hy => hsball (ball_subset_ball (min_le_right _ _) hy)),?_⟩
    intro y hy
    obtain ⟨hyU,hyV,hyA⟩ := hball (ball_subset_ball (min_le_left _ _) hy)
    refine ⟨hyU,?_⟩
    change (y ∈ U ∧ IsUnit (A y)) ↔ d y.val ≠ 0
    rw [and_iff_right hyU,hyA]
    exact hcrit y.val hyV

end NLS.Coeff
