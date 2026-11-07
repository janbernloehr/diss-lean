import NLS.SequenceSpaces.WeightedDomination

/-! Raw weighted coefficient bounds against an unweighted lp majorant
construct the actual weighted target, including exponent infinity. -/
noncomputable section
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem exists_of_weighted_norm_le (w : Weight) (a : Coeff p) (f : ℤ → ℂ)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ k, ‖(w k:ℂ)*f k‖ ≤ C*‖a k‖) :
    ∃ b : WeightedCoeff w p, (∀ k, b.val k = f k) ∧ ‖b‖ ≤ C*‖a‖ := by
  have hmem : Memℓp (fun k => (w k:ℂ)*f k) p :=
    ((lp.memℓp a).norm.const_mul C).mono (by intro k; simpa only [norm_mul,Real.norm_eq_abs,abs_of_nonneg hC] using hf k)
  let b : WeightedCoeff w p := ⟨f,hmem⟩
  have h : ‖weightEquiv w p b‖ ≤ ‖(C:ℂ) • a‖ := by
    apply lp.norm_mono (ne_of_gt (lt_of_lt_of_le zero_lt_one Fact.out))
    intro k
    simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg hC,weightEquiv_apply] using hf k
  refine ⟨b,fun _ => rfl,?_⟩
  simpa only [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,← norm_eq] using h

end NLS.WeightedCoeff
