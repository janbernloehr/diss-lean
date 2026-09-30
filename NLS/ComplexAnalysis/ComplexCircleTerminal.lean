import NLS.ComplexAnalysis.ParametricTrigonometricTerminal
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex

/-! # Analytic angles at arbitrary complex circle coordinates

Every complex sine/cosine pair on the algebraic circle has an angle.
Its analytic continuation fixes both coordinates, including sine zeros.
The base point need not lie on a real gap segment.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis

theorem exists_angle_of_sine_sq_add_cosine_sq (S C : ℂ)
    (hsq : S ^ 2 + C ^ 2 = 1) :
    ∃ e : ℂ, Complex.sin e = S ∧ Complex.cos e = C := by
  obtain ⟨e,he⟩ := Complex.cos_surjective C
  have hsinSq : Complex.sin e ^ 2 = S ^ 2 := by
    have htrig := Complex.sin_sq_add_cos_sq e
    rw [he] at htrig
    linear_combination htrig - hsq
  rcases eq_or_eq_neg_of_sq_eq_sq (Complex.sin e) S hsinSq with h | h
  · exact ⟨e,h,he⟩
  · exact ⟨-e,by simp only [Complex.sin_neg,h,neg_neg],by rwa [Complex.cos_neg]⟩

/-- Reversing both circle coordinates changes an angle only modulo pi. -/
theorem angle_sub_eq_int_pi_of_coordinates_up_to_sign
    (e f κ : ℂ) (hκ : κ = 1 ∨ κ = -1)
    (hsin : Complex.sin e = κ * Complex.sin f)
    (hcos : Complex.cos e = κ * Complex.cos f) :
    ∃ k : ℤ, e - f = (k : ℂ) * (Real.pi : ℂ) := by
  rcases hκ with rfl | rfl
  · obtain ⟨k,hk⟩ := eq_mod_two_pi_of_cos_eq_of_sin_eq e f
      (by simpa only [one_mul] using hcos) (by simpa only [one_mul] using hsin)
    refine ⟨2 * k,?_⟩
    push_cast
    linear_combination hk
  · obtain ⟨k,hk⟩ := eq_mod_two_pi_of_cos_eq_of_sin_eq e (f + (Real.pi : ℂ))
      (by simpa only [Complex.cos_add_pi,neg_one_mul] using hcos)
      (by simpa only [Complex.sin_add_pi,neg_one_mul] using hsin)
    refine ⟨2 * k + 1,?_⟩
    push_cast
    linear_combination hk

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]

/-- The analytic circle identity constructs a moving terminal angle
without requiring a base angle as input. -/
theorem exists_analytic_parametricCosine_terminal_from_circle
    (τ δ μ σ : A → ℂ) (a : A)
    (hτ : AnalyticAt ℂ τ a) (hδ : AnalyticAt ℂ δ a)
    (hμ : AnalyticAt ℂ μ a) (hσ : AnalyticAt ℂ σ a)
    (hδne : δ a ≠ 0)
    (hsq : ∀ᶠ b in 𝓝 a, σ b ^ 2 + ((μ b - τ b) / δ b) ^ 2 = 1) :
    ∃ ε : A → ℂ, AnalyticAt ℂ ε a ∧
      ∀ᶠ b in 𝓝 a, cosineGapPoint (τ b) (δ b) (ε b) = μ b ∧
        Complex.sin (ε b) = σ b := by
  obtain ⟨e,hsin,hcos⟩ := exists_angle_of_sine_sq_add_cosine_sq
    (σ a) ((μ a - τ a) / δ a) hsq.self_of_nhds
  have hpoint : cosineGapPoint (τ a) (δ a) e = μ a := by
    dsimp only [cosineGapPoint]
    rw [hcos,mul_div_cancel₀ _ hδne]
    ring
  obtain ⟨ε,hε,_,hterminal⟩ := exists_analytic_parametricCosine_terminal_with_sine
    τ δ μ σ a e hτ hδ hμ hσ hδne hsin.symm hpoint hsq
  exact ⟨ε,hε,hterminal⟩

end NLS.ComplexAnalysis
