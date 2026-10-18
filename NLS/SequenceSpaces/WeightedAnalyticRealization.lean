import NLS.SequenceSpaces.LocallyBoundedRealization
import NLS.SequenceSpaces.WeightedFiniteCoefficients

/-! # Analytic realization in weighted sequence spaces

Analytic scalar coefficients with locally bounded weighted realizations define an analytic map into the actual weighted Banach target. The result includes exponent infinity and identifies every unweighted coefficient.
-/

noncomputable section
open Set Metric Complex Filter Topology
open scoped ENNReal

namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A total weighted realization of scalar coefficients, with its local value fixed by the membership theorems below. -/
def ofFunctionOrZero (w : Weight) (p : ℝ≥0∞) (f : ℤ → ℂ) : WeightedCoeff w p :=
  (weightEquiv w p).symm (Coeff.ofFunctionOrZero p (fun n => (w n:ℂ)*f n))

omit [Fact (1 ≤ p)] in
/-- The weighted realization agrees with any actual sequence with those coefficients. -/
theorem ofFunctionOrZero_eq_of_coordinates (w : Weight) (f : ℤ → ℂ) (b : WeightedCoeff w p)
    (hb : ∀ n, b.val n = f n) : ofFunctionOrZero w p f = b := by
  apply (weightEquiv w p).injective
  simp only [ofFunctionOrZero,LinearEquiv.apply_symm_apply]
  apply Coeff.ofFunctionOrZero_eq_of_coordinates
  intro n
  simp only [weightEquiv_apply,hb]

/-- Uniformly bounded weighted realizations and analytic raw coefficients give an analytic map into that weighted Banach space. -/
theorem analytic_realization_of_bound (w : Weight) (f : E → ℤ → ℂ) {U : Set E}
    (hU : IsOpen U) (ha : ∀ n, AnalyticOnNhd ℂ (fun ψ => f ψ n) U)
    (M : ℝ) (hb : ∀ ψ ∈ U, ∃ b : WeightedCoeff w p, (∀ n, b.val n = f ψ n) ∧ ‖b‖ ≤ M) :
    AnalyticOnNhd ℂ (fun ψ => ofFunctionOrZero w p (f ψ)) U ∧
      ∀ ψ ∈ U, ‖ofFunctionOrZero w p (f ψ)‖ ≤ M ∧ ∀ n, (ofFunctionOrZero w p (f ψ)).val n = f ψ n := by
  let g : E → ℤ → ℂ := fun ψ n => (w n:ℂ)*f ψ n
  have hg (n : ℤ) : AnalyticOnNhd ℂ (fun ψ => g ψ n) U := fun ψ hψ => analyticAt_const.mul (ha n ψ hψ)
  have hbg (ψ : E) (hψ : ψ ∈ U) : ∃ b : Coeff p, (∀ n, b n = g ψ n) ∧ ‖b‖ ≤ M := by
    obtain ⟨b,hb,hn⟩ := hb ψ hψ
    refine ⟨weightEquiv w p b,?_,hn⟩
    intro n
    simp only [weightEquiv_apply,hb,g]
  obtain ⟨_,hga⟩ := Coeff.analytic_realization_of_local_bounds g hU hg
    (fun ψ hψ => ⟨U,hU,hψ,Subset.rfl,M,hbg⟩)
  refine ⟨?_,?_⟩
  · intro ψ hψ
    exact ((weightIsometry w p).symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp (hga ψ hψ)
  · intro ψ hψ
    obtain ⟨b,hb,hn⟩ := hb ψ hψ
    rw [ofFunctionOrZero_eq_of_coordinates w (f ψ) b hb]
    exact ⟨hn,hb⟩

end NLS.WeightedCoeff
