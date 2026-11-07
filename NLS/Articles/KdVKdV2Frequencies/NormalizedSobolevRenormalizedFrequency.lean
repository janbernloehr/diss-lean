import NLS.Articles.KdVKdV2Frequencies.NormalizedSobolevWeakActions

/-! The SAME global weak scalar frequency plus the literal original
counterterm, in normalized Sobolev action coordinates. -/
noncomputable section
set_option autoImplicit false
open Set Complex NLS.KdV NLS.Articles.KdVConvexity
open scoped ENNReal
namespace NLS.Articles.KdVKdV2Frequencies

def normalizedSobolevRenormalizedFrequency (α : ℝ) (hα : -1≤α)
    (G : ℕ+ → Coeff 1 → ℂ) (n : ℕ+) (a : Coeff 1) : ℂ :=
  G n (normalizedSobolevWeakActionInclusion α hα a)+
    6*(a (actionIndexEquiv.symm n)/(Weight.sobolev α (n:ℤ) : ℂ))

theorem normalizedSobolevRenormalizedFrequency_analytic
    (α : ℝ) (hα : -1≤α) (G : ℕ+ → Coeff 1 → ℂ) (V : Set (Coeff 1))
    (hG : ∀ n, AnalyticOnNhd ℂ (G n) V) (n : ℕ+) :
    AnalyticOnNhd ℂ (normalizedSobolevRenormalizedFrequency α hα G n)
      (normalizedSobolevWeakActionInclusion α hα ⁻¹' V) := by
  intro a ha
  exact ((hG n _ ha).comp ((normalizedSobolevWeakActionInclusion α hα).analyticAt a)).add
    (analyticAt_const.mul (((lp.evalCLM ℂ (fun _ : ℤ => ℂ) 1 (actionIndexEquiv.symm n)).analyticAt a).div_const))

end NLS.Articles.KdVKdV2Frequencies
