import NLS.ComplexAnalysis.ParametricCosineTerminal
import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-!
# Analytic terminal angles at critical cosine points

The sine coordinate is regular at a cosine endpoint. Its analytic local
inverse constructs a moving angle. A spectral square identity and the
nonzero base cosine fix the cosine sign and recover the exact terminal.
-/

noncomputable section
open Set Complex Filter Topology
namespace NLS.ComplexAnalysis
variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- Prescribing an analytic sine gives an analytic angle near a regular
sine point. Every source with the base sine has exactly the base angle. -/
theorem exists_analytic_parametricSine_terminal
    (σ : A → ℂ) (a : A) (e : ℂ) (hσ : AnalyticAt ℂ σ a)
    (hcos : Complex.cos e ≠ 0) (hbase : σ a = Complex.sin e) :
    ∃ ε : A → ℂ, AnalyticAt ℂ ε a ∧ ε a = e ∧
      (∀ᶠ b in 𝓝 a, Complex.sin (ε b) = σ b) ∧
      ∀ b : A, σ b = Complex.sin e → ε b = e := by
  have hs : AnalyticAt ℂ Complex.sin e := Complex.analyticAt_sin
  have hne : deriv Complex.sin e ≠ 0 := by rw [(Complex.hasDerivAt_sin e).deriv]; exact hcos
  let inv := hs.hasStrictDerivAt.localInverse Complex.sin (deriv Complex.sin e) e hne
  have hi : AnalyticAt ℂ inv (Complex.sin e) := hs.analyticAt_localInverse hne
  have hie : inv (Complex.sin e) = e := HasStrictFDerivAt.localInverse_apply_image ..
  have hir : ∀ᶠ z in 𝓝 (Complex.sin e), Complex.sin (inv z) = z :=
    HasStrictDerivAt.eventually_right_inverse ..
  let ε : A → ℂ := fun b => inv (σ b)
  have hε : AnalyticAt ℂ ε a := hi.comp_of_eq (f := σ) hσ hbase
  have heq : ∀ᶠ b in 𝓝 a, Complex.sin (ε b) = σ b := by
    have ht : Tendsto σ (𝓝 a) (𝓝 (Complex.sin e)) := hbase ▸ hσ.continuousAt.tendsto
    exact ht.eventually hir
  exact ⟨ε,hε,by dsimp [ε]; rw [hbase,hie],heq,fun b hb => by dsimp [ε]; rw [hb,hie]⟩

/-- A normalized spectral identity fixes the cosine sign near a
nonzero base cosine, even when sine and the terminal root vanish. -/
theorem exists_analytic_parametricCosine_terminal_from_sine
    (τ δ μ σ : A → ℂ) (a : A) (e : ℂ)
    (hτ : AnalyticAt ℂ τ a) (hδ : AnalyticAt ℂ δ a)
    (hμ : AnalyticAt ℂ μ a) (hσ : AnalyticAt ℂ σ a)
    (hδne : δ a ≠ 0) (hcos : Complex.cos e ≠ 0)
    (hsinbase : σ a = Complex.sin e) (hcosbase : Complex.cos e = (μ a-τ a)/δ a)
    (hsq : ∀ᶠ b in 𝓝 a, σ b^2+((μ b-τ b)/δ b)^2 = 1) :
    ∃ ε : A → ℂ, AnalyticAt ℂ ε a ∧ ε a = e ∧
      (∀ᶠ b in 𝓝 a, cosineGapPoint (τ b) (δ b) (ε b) = μ b ∧ Complex.sin (ε b) = σ b) ∧
      ∀ b : A, σ b = Complex.sin e → ε b = e := by
  obtain ⟨ε,hε,hεa,hsin,hbase⟩ := exists_analytic_parametricSine_terminal σ a e hσ hcos hsinbase
  let X : A → ℂ := fun b => (μ b-τ b)/δ b
  have hX : AnalyticAt ℂ X a := (hμ.sub hτ).div hδ hδne
  have hcoscont : ContinuousAt (fun b => Complex.cos (ε b)) a :=
    Complex.continuous_cos.continuousAt.comp hε.continuousAt
  have heq : (fun b => Complex.cos (ε b)) =ᶠ[𝓝 a] X := by
    apply eventuallyEq_of_sq_eq_of_continuousAt _ X a hcoscont hX.continuousAt
      (by rw [hεa]; exact hcosbase) (by change (μ a-τ a)/δ a ≠ 0; rw [← hcosbase]; exact hcos)
    filter_upwards [hsin,hsq] with b hb hsqb
    have htrig := Complex.sin_sq_add_cos_sq (ε b)
    rw [hb] at htrig
    linear_combination htrig-hsqb
  refine ⟨ε,hε,hεa,?_,hbase⟩
  filter_upwards [heq,hsin,hδ.continuousAt.eventually_ne hδne] with b hcosb hsinb hδb
  refine ⟨?_,hsinb⟩
  dsimp only [cosineGapPoint]
  rw [hcosb]
  dsimp only [X]
  rw [mul_div_cancel₀ _ hδb]
  exact add_sub_cancel _ _

end NLS.ComplexAnalysis
