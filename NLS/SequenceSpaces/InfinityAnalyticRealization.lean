import NLS.SequenceSpaces.LocallyBoundedRealization

/-! Uniform scalar bounds realize analytic maps in the actual
unweighted infinity norm, with every coefficient retained. -/
noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.Coeff
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem analytic_infty_realization_of_bound (f : E → ℤ → ℂ)
    {U : Set E} (hU : IsOpen U) (ha : ∀ k, AnalyticOnNhd ℂ (fun x => f x k) U)
    (C : ℝ) (hC : 0 ≤ C) (hb : ∀ x ∈ U, ∀ k, ‖f x k‖ ≤ C) :
    AnalyticOnNhd ℂ (fun x => ofFunctionOrZero ⊤ (f x)) U ∧
      ∀ x ∈ U, ‖ofFunctionOrZero ⊤ (f x)‖ ≤ C ∧
        ∀ k, ofFunctionOrZero ⊤ (f x) k = f x k := by
  have hreal (x : E) (hx : x ∈ U) :
      ∃ b : Coeff ⊤, (∀ k, b k=f x k) ∧ ‖b‖ ≤ C := by
    have hm : Memℓp (f x) ⊤ := memℓp_infty ⟨C,by rintro _ ⟨k,rfl⟩; exact hb x hx k⟩
    exact ⟨⟨f x,hm⟩,fun _ => rfl,lp.norm_le_of_forall_le hC (hb x hx)⟩
  obtain ⟨hc,hA⟩ := analytic_realization_of_local_bounds f hU ha
    (fun x hx => ⟨U,hU,hx,Subset.rfl,C,hreal⟩)
  refine ⟨hA,fun x hx => ⟨?_,hc x hx⟩⟩
  obtain ⟨b,hb,hn⟩ := hreal x hx
  rwa [ofFunctionOrZero_eq_of_coordinates _ b hb]

end NLS.Coeff
