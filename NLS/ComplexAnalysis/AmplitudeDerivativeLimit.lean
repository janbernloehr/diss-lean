import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Tactic.FieldSimp

/-! # Recovering a closed-action frequency from an amplitude derivative

If an analytic physical energy satisfies `H'(a)=a*omega(a)` along a
nonzero sequence approaching zero, the frequency limit is `H''(0)`.
-/
noncomputable section
open Filter Topology Complex
namespace NLS.ComplexAnalysis

theorem second_deriv_eq_of_amplitude_frequency_limit
    (H : ℝ → ℂ) (hH : AnalyticAt ℝ H 0) (a : ℕ → ℝ) (ω : ℕ → ℂ) (L : ℂ)
    (ha : Tendsto a atTop (𝓝 0)) (hane : ∀ k, a k ≠ 0)
    (hω : Tendsto ω atTop (𝓝 L))
    (hd : ∀ k, deriv H (a k) = (a k : ℂ)*ω k) :
    deriv H 0 = 0 ∧ deriv (deriv H) 0 = L := by
  have hz : deriv H 0 = 0 := by
    have h₁ := hH.deriv.continuousAt.tendsto.comp ha
    have h₂ : Tendsto (fun k => (a k : ℂ)*ω k) atTop (𝓝 (0 : ℂ)) := by
      simpa only [Complex.ofReal_zero,zero_mul] using! (Complex.continuous_ofReal.tendsto 0 |>.comp ha).mul hω
    exact tendsto_nhds_unique h₁ (h₂.congr (fun k => (hd k).symm))
  refine ⟨hz,?_⟩
  have haNE : Tendsto a atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨ha,Eventually.of_forall (fun k => hane k)⟩
  have hs := hH.deriv.differentiableAt.hasDerivAt.tendsto_slope.comp haNE
  have he (k : ℕ) : slope (deriv H) 0 (a k) = ω k := by
    simp only [slope,vsub_eq_sub,sub_zero,hz,hd,Complex.real_smul]
    push_cast
    field_simp [show (a k : ℂ) ≠ 0 by exact_mod_cast hane k]
  exact tendsto_nhds_unique (hs.congr he) hω

end NLS.ComplexAnalysis
