import NLS.FunctionalAnalysis.CompactAnalyticDeterminant
import NLS.ComplexAnalysis.LocalAnalyticNonvanishing

/-! # Generic invertibility of analytic compact perturbations

The local Schur determinants and the identity theorem prove the density
argument used in Proposition I.4 and Corollary 18.2(iv).
-/
noncomputable section
open Set Filter Topology
namespace NLS.CompactSpectrum
variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup X] [NormedSpace ℂ X]

/-- In a connected open analytic family of compact scalar perturbations,
one invertible member implies an open dense set of invertible members. -/
theorem open_dense_isUnit_of_analytic_compact_shift
    {A : X → E →L[ℂ] E} {U : Set X} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hA : AnalyticOnNhd ℂ A U) {c : ℂ} (hc : c ≠ 0)
    (hcompact : ∀ x ∈ U, IsCompactOperator (A x - c • 1 : E →L[ℂ] E))
    (hstart : ∃ x ∈ U, IsUnit (A x)) :
    IsOpen {x ∈ U | IsUnit (A x)} ∧ U ⊆ closure {x ∈ U | IsUnit (A x)} := by
  have hS : IsOpen {x ∈ U | IsUnit (A x)} :=
    hA.continuousOn.isOpen_inter_preimage hU Units.isOpen
  refine ⟨hS, NLS.ComplexAnalysis.subset_closure_of_local_analytic_nonvanishing hU hconn hS ?_ ?_⟩
  · obtain ⟨x,hx,hu⟩ := hstart
    exact ⟨x,hx,hx,hu⟩
  · intro x hx
    obtain ⟨V,hV,hxV,d,hd,hcrit⟩ := exists_local_analytic_determinant (hA x hx) hc (hcompact x hx)
    refine ⟨V,hV,hxV,d,hd,?_⟩
    intro y hy
    exact and_iff_right hy.2 |>.trans (hcrit y hy.1)

end NLS.CompactSpectrum
