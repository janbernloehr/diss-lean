import NLS.SequenceSpaces.RealActionBallGluing

/-! # Analytic continuation of the refined action correction identity

Scalar uniqueness propagates the identity between maps with different
Banach target exponents to the whole complex action domain.
-/
noncomputable section
open Set
open scoped ENNReal
namespace NLS.Coeff
variable {q r s : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)] [Fact (1 ≤ s)]

/-- The frequency-plus-twice-action formula extends from real representatives
to the full domain, even when the two maps have different target norms. -/
theorem actionCorrection_eq_of_analytic_uniqueness {α : Type*}
    (a : α → Coeff q) (V : Set (Coeff q))
    (huniq : ∀ f g : Coeff q → ℂ, AnalyticOnNhd ℂ f V → AnalyticOnNhd ℂ g V →
      (∀ i, f (a i) = g (a i)) → EqOn f g V)
    (F : Coeff q → Coeff r) (H : Coeff q → Coeff s)
    (hF : AnalyticOnNhd ℂ F V) (hH : AnalyticOnNhd ℂ H V)
    (he : ∀ i n, H (a i) n = F (a i) n+2*a i n) :
    ∀ b ∈ V, ∀ n, H b n = F b n+2*b n := by
  intro b hb n
  have hh : AnalyticOnNhd ℂ (fun c => H c n) V := fun c hc =>
    ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) s n).analyticAt _).comp (hH c hc)
  have hf : AnalyticOnNhd ℂ (fun c => F c n+2*c n) V := fun c hc =>
    (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) r n).analyticAt _).comp (hF c hc)).add
      (analyticAt_const.mul ((lp.evalCLM ℂ (fun _ : ℤ => ℂ) q n).analyticAt c))
  exact huniq _ _ hh hf (fun i => he i n) hb

end NLS.Coeff
