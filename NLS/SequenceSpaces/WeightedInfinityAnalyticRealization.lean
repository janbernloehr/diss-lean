import NLS.SequenceSpaces.WeightedAnalyticRealization

/-! Uniform weighted scalar bounds give an analytic realization in the
actual weighted infinity Banach space, retaining every raw coefficient. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_infty_realization_of_weighted_bound (w : Weight) (f : E → ℤ → ℂ)
    {U : Set E} (hU : IsOpen U) (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x ∈ U, ∀ k, w k * ‖f x k‖ ≤ C) :
    AnalyticOnNhd ℂ (fun x => ofFunctionOrZero w ⊤ (f x)) U ∧
      ∀ x ∈ U, ‖ofFunctionOrZero w ⊤ (f x)‖ ≤ C ∧
        ∀ k, (ofFunctionOrZero w ⊤ (f x)).val k = f x k := by
  apply analytic_realization_of_bound w f hU ha C
  intro x hx
  have hpoint (k : ℤ) : ‖(w k : ℂ) * f x k‖ ≤ C := by
    simpa only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (w.positive k)] using hb x hx k
  have hm : Memℓp (fun k => (w k : ℂ) * f x k) ⊤ :=
    memℓp_infty ⟨C,by rintro _ ⟨k,rfl⟩; exact hpoint k⟩
  let b : WeightedCoeff w ⊤ := ⟨f x,hm⟩
  refine ⟨b,fun _ => rfl,?_⟩
  change ‖weightEquiv w ⊤ b‖ ≤ C
  exact lp.norm_le_of_forall_le hC hpoint

end NLS.WeightedCoeff
