import NLS.ComplexAnalysis.AnalyticImplicitBanachRoot

/-! Local analytic scalar zeros with a Banach parameter, constructed
from a nonzero partial derivative without a preselected root function. -/
noncomputable section
open Set Filter
open scoped Topology
namespace NLS.ComplexAnalysis

/-- A simple zero of a jointly analytic scalar equation extends to an
analytic local zero selection on the entire complex Banach parameter space. -/
theorem exists_analytic_implicitScalarRoot
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] [CompleteSpace P]
    (F : ℂ × P → ℂ) (a : ℂ) (x : P) (hF : AnalyticAt ℂ F (a,x))
    (hzero : F (a,x) = 0) (hsimple : (fderiv ℂ F (a,x)) (1,0) ≠ 0) :
    ∃ s : P → ℂ, AnalyticAt ℂ s x ∧ s x = a ∧
      ∀ᶠ y in 𝓝 x, F (s y,y) = 0 := by
  apply exists_analytic_implicitBanachRoot F a x hF hzero
  let A := fderiv ℂ F (a,x)
  have he (z : ℂ) : A (z,0) = z*A (1,0) := by
    have hvec : (z,(0:P)) = z • (1,(0:P)) := by ext <;> simp
    rw [hvec,map_smul,smul_eq_mul]
  constructor
  · intro z w h
    change A (z,0) = A (w,0) at h
    rw [he z,he w] at h
    exact mul_right_cancel₀ hsimple h
  · intro y
    refine ⟨y/A (1,0),?_⟩
    change A (y/A (1,0),0) = y
    rw [he,div_mul_cancel₀ _ hsimple]

end NLS.ComplexAnalysis
