import NLS.ZakharovShabat.Lemma272ConstantBudget

/-! # What the mass and kinetic estimates imply at the endpoint of Lemma 27.2

These are scalar implications, not counterexamples involving spectral data.
-/
namespace NLS.ZakharovShabat

/-- The exact maximum of the available energy budget over masses between zero and S. -/
theorem lemma272_mass_budget_le_max (M S : ℝ) (hM : 0 ≤ M) (hMS : M ≤ S) :
    S-M+2*M^2 ≤ max S (2*S^2) := by
  have hcross := mul_nonneg hM (sub_nonneg.mpr hMS)
  by_cases h : 2*S ≤ 1
  · have hprod := mul_nonneg hM (by linarith : 0 ≤ 1-2*S)
    exact (by nlinarith : S-M+2*M^2 ≤ S).trans (le_max_left _ _)
  · have hprod := mul_nonneg (sub_nonneg.mpr hMS) (by linarith : 0 ≤ 2*S-1)
    exact (by nlinarith : S-M+2*M^2 ≤ 2*S^2).trans (le_max_right _ _)

/-- Both endpoint values M=0 and M=S are allowed by these scalar hypotheses. -/
theorem lemma272_mass_budget_uniform_iff (S B : ℝ) (hS : 0 ≤ S) :
    (∀ M : ℝ, 0 ≤ M → M ≤ S → S-M+2*M^2 ≤ B) ↔ max S (2*S^2) ≤ B := by
  constructor
  · intro h
    exact max_le (by simpa using h 0 le_rfl hS) (by simpa using h S hS le_rfl)
  · intro h M hM hMS
    exact (lemma272_mass_budget_le_max M S hM hMS).trans h

/-- The printed endpoint follows uniformly from this budget exactly when S ≤ 2. -/
theorem lemma272_endpoint_budget_iff (S : ℝ) (hS : 0 ≤ S) :
    (∀ M : ℝ, 0 ≤ M → M ≤ S → S-M+2*M^2 ≤ 2*S+S^2) ↔ S ≤ 2 := by
  rw [lemma272_mass_budget_uniform_iff S _ hS, max_le_iff]
  constructor
  · rintro ⟨_,h⟩
    nlinarith
  · intro h
    constructor <;> nlinarith

/-- An explicit failure of the scalar implication, not an example of a potential. -/
theorem lemma272_endpoint_scalar_obstruction :
    (0:ℝ) ≤ 3 ∧ (3:ℝ) ≤ 3 ∧ ¬ ((3:ℝ)-3+2*3^2 ≤ 2*3+3^2) := by
  norm_num

end NLS.ZakharovShabat
