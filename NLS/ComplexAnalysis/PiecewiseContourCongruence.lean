import NLS.ComplexAnalysis.PiecewiseC1Loop
import NLS.ComplexAnalysis.CurveIntegralInteriorCongruence

/-! # Congruence of actual piecewise contour integrals -/

noncomputable section
open Set
namespace NLS.ComplexAnalysis.PiecewiseC1Loop

/-- Only values on the contour affect its integral; no continuity is required. -/
theorem integral_congr (Γ : PiecewiseC1Loop) {D : Set ℂ} {f g : ℂ → ℂ}
    (hΓ : Γ.Inside D) (hfg : EqOn f g D) : Γ.integral f = Γ.integral g := by
  apply Finset.sum_congr rfl
  intro i _
  apply curveIntegral_holomorphicOneForm_congr_interior
  intro t ht
  rw [Path.extend_apply (Γ.edge i) ⟨ht.1.le,ht.2.le⟩]
  exact hfg (hΓ i ⟨t,ht.1.le,ht.2.le⟩)

end NLS.ComplexAnalysis.PiecewiseC1Loop
