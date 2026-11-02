import NLS.ComplexAnalysis.ParametricDividedDifference

/-! # Filled moving division depends only on its actual scalar slice -/
noncomputable section
namespace NLS.ComplexAnalysis
variable {A B : Type}

theorem parametricMovingDividedDifference_congr_slice
    (F : ℂ × A → ℂ) (G : ℂ × B → ℂ) (mu : A → ℂ) (nu : B → ℂ)
    (a : A) (b : B) (z : ℂ) (hcenter : mu a = nu b)
    (hslice : ∀ w : ℂ, F (w,a) = G (w,b)) :
    parametricMovingDividedDifference F mu (z,a) = parametricMovingDividedDifference G nu (z,b) := by
  have he : (fun w : ℂ => F (mu a+w,a)) = (fun w : ℂ => G (nu b+w,b)) := by
    funext w
    rw [hcenter,hslice]
  change (∫ t in (0 : ℝ)..1, deriv (fun w : ℂ => F (mu a+w,a)) ((t : ℂ)*(z-mu a))) =
    ∫ t in (0 : ℝ)..1, deriv (fun w : ℂ => G (nu b+w,b)) ((t : ℂ)*(z-nu b))
  rw [he,hcenter]

end NLS.ComplexAnalysis
