import NLS.ComplexAnalysis.ParametricSineTerminal
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# Analytic terminal angles with both trigonometric coordinates

The sine and cosine cannot both have a zero derivative. A prescribed
base angle and an analytic circle identity therefore give an analytic
moving angle at every terminal, including either cosine endpoint.
Both coordinates are fixed, so compatible angles differ by an integer
multiple of two pi.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A]

/-- An analytic terminal and sine coordinate determine an analytic
angle through every prescribed base angle, including sine zeros. -/
theorem exists_analytic_parametricCosine_terminal_with_sine
    (τ δ μ σ : A → ℂ) (a : A) (e : ℂ)
    (hτ : AnalyticAt ℂ τ a) (hδ : AnalyticAt ℂ δ a)
    (hμ : AnalyticAt ℂ μ a) (hσ : AnalyticAt ℂ σ a)
    (hδne : δ a ≠ 0) (hsinbase : σ a = Complex.sin e)
    (hpoint : cosineGapPoint (τ a) (δ a) e = μ a)
    (hsq : ∀ᶠ b in 𝓝 a, σ b^2 + ((μ b - τ b) / δ b)^2 = 1) :
    ∃ ε : A → ℂ, AnalyticAt ℂ ε a ∧ ε a = e ∧
      ∀ᶠ b in 𝓝 a, cosineGapPoint (τ b) (δ b) (ε b) = μ b ∧ Complex.sin (ε b) = σ b := by
  have hcosbase : Complex.cos e = (μ a - τ a) / δ a := by
    apply (eq_div_iff hδne).mpr
    dsimp only [cosineGapPoint] at hpoint
    linear_combination hpoint
  by_cases hcos : Complex.cos e ≠ 0
  · obtain ⟨ε,hε,hεa,hzeros,_⟩ := exists_analytic_parametricCosine_terminal_from_sine
      τ δ μ σ a e hτ hδ hμ hσ hδne hcos hsinbase hcosbase hsq
    exact ⟨ε,hε,hεa,hzeros⟩
  · have hsin : Complex.sin e ≠ 0 := by
      intro hs
      have hid := Complex.sin_sq_add_cos_sq e
      rw [hs,not_ne_iff.mp hcos] at hid
      norm_num at hid
    obtain ⟨ε,hε,hεa,hzeros⟩ := exists_analytic_parametricCosine_terminal
      τ δ μ a e hτ hδ hμ hδne hsin hpoint
    have hsincont : ContinuousAt (fun b => Complex.sin (ε b)) a :=
      Complex.continuous_sin.continuousAt.comp hε.continuousAt
    have heq : (fun b => Complex.sin (ε b)) =ᶠ[𝓝 a] σ := by
      apply eventuallyEq_of_sq_eq_of_continuousAt _ σ a hsincont hσ.continuousAt
        (by rw [hεa]; exact hsinbase.symm) (hsinbase ▸ hsin)
      filter_upwards [hzeros,hsq,hδ.continuousAt.eventually_ne hδne] with b hb hsqb hδb
      have hcosb : Complex.cos (ε b) = (μ b - τ b) / δ b := by
        apply (eq_div_iff hδb).mpr
        dsimp only [cosineGapPoint] at hb
        linear_combination hb
      have htrig := Complex.sin_sq_add_cos_sq (ε b)
      rw [hcosb] at htrig
      linear_combination htrig - hsqb
    exact ⟨ε,hε,hεa,by
      filter_upwards [hzeros,heq] with b hb hs
      exact ⟨hb,hs⟩⟩

omit [NormedAddCommGroup A] [NormedSpace ℂ A] [CompleteSpace A] in
/-- Fixing both sine and cosine fixes the angle modulo two pi. -/
theorem eq_mod_two_pi_of_cos_eq_of_sin_eq (e f : ℂ)
    (hcos : Complex.cos e = Complex.cos f) (hsin : Complex.sin e = Complex.sin f) :
    ∃ k : ℤ, e = f + (k : ℂ) * (2 * (Real.pi : ℂ)) := by
  have hexp : Complex.exp (e * I) = Complex.exp (f * I) := by
    rw [Complex.exp_mul_I,Complex.exp_mul_I,hcos,hsin]
  obtain ⟨k,hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hI : I * (-I) = 1 := by simp
  refine ⟨k,?_⟩
  simpa only [add_mul,mul_assoc,hI,mul_one] using congrArg (fun z : ℂ => z * (-I)) hk

end NLS.ComplexAnalysis
