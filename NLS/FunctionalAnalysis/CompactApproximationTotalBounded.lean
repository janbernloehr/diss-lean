import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
import Mathlib.Analysis.Complex.Basic

/-! Total boundedness from common compact linear approximations. -/
noncomputable section
open Set Metric
namespace NLS

theorem totallyBounded_of_bounded_compact_approximations
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (B : Set E) (hB : Bornology.IsBounded B)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ A : E →L[ℂ] E,
      IsCompactOperator A ∧ ∀ x ∈ B, ‖x-A x‖ ≤ ε) : TotallyBounded B := by
  apply Metric.totallyBounded_iff.mpr
  intro ε hε
  obtain ⟨A,hA,herror⟩ := happrox (ε/2) (half_pos hε)
  have hK := hA.isCompact_closure_image_of_bounded hB
  obtain ⟨s,hs,hcover⟩ := Metric.totallyBounded_iff.mp hK.totallyBounded (ε/2) (half_pos hε)
  refine ⟨s,hs,?_⟩
  intro x hx
  have hc := hcover (subset_closure (show A x ∈ A '' B from ⟨x,hx,rfl⟩))
  simp only [mem_iUnion] at hc ⊢
  obtain ⟨y,hy,hnear⟩ := hc
  refine ⟨y,hy,?_⟩
  rw [Metric.mem_ball] at hnear ⊢
  have he : dist x (A x) ≤ ε/2 := by simpa only [dist_eq_norm] using herror x hx
  have ht := dist_triangle x (A x) y
  linarith

end NLS
