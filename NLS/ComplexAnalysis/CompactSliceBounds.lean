import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Constructions.SumProd

/-! # Uniform norm bounds near compact parameter slices -/
noncomputable section
open Set Metric Complex
namespace NLS.ComplexAnalysis
/-- A strict bound on a compact slice persists on one parameter neighborhood. -/
theorem exists_compact_slice_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (F : ℂ × E → ℂ) (O : Set (ℂ × E)) (hO : IsOpen O)
    (hF : ContinuousOn F O) (S : Set ℂ) (hS : IsCompact S) (a : E) (B : ℝ)
    (hcover : ∀ z ∈ S, (z,a) ∈ O) (hbound : ∀ z ∈ S, ‖F (z,a)‖ < B) :
    ∃ U : Set E, IsOpen U ∧ a ∈ U ∧ ∀ q ∈ U, ∀ z ∈ S, ‖F (z,q)‖ ≤ B := by
  let W := O ∩ (fun t => ‖F t‖) ⁻¹' Iio B
  have hW : IsOpen W := hF.norm.isOpen_inter_preimage hO isOpen_Iio
  have hs : S ×ˢ {a} ⊆ W := by
    rintro ⟨z,q⟩ ⟨hz,hq⟩
    obtain rfl := mem_singleton_iff.mp hq
    exact ⟨hcover z hz,hbound z hz⟩
  obtain ⟨V,U,_,hU,hSV,ha,hsub⟩ := generalized_tube_lemma hS isCompact_singleton hW hs
  exact ⟨U,hU,ha (mem_singleton _),fun q hq z hz => (hsub ⟨hSV hz,hq⟩).2.le⟩
end NLS.ComplexAnalysis
