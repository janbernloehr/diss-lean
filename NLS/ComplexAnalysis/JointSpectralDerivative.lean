import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FunProp

/-!
# Spectral derivatives of jointly analytic families

For a holomorphic family on a product of a spectral line and a
complex Banach parameter space, differentiating in the spectral
coordinate gives a jointly continuous function. The spectral
derivative is the joint Fréchet derivative applied to `(1, 0)`.
-/

noncomputable section
open Set
namespace NLS.ComplexAnalysis

variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

/-- The spectral derivative of a jointly differentiable family is
the joint Fréchet derivative in the spectral coordinate. -/
theorem deriv_spectral_section_eq_fderiv
    (F : ℂ × A → ℂ) (z : ℂ) (a : A)
    (hF : DifferentiableAt ℂ F (z,a)) :
    deriv (fun w : ℂ => F (w,a)) z =
      (fderiv ℂ F (z,a)) (1,0) := by
  have hinc : HasDerivAt (fun w : ℂ => (w,a)) (1,0) z := by
    simpa using (hasDerivAt_id z).prodMk (hasDerivAt_const z a)
  exact (hF.hasFDerivAt.comp_hasDerivAt z hinc).deriv

/-- The spectral derivative varies continuously in both spectral
point and complex Banach parameter on an open analytic domain. -/
theorem continuousOn_spectral_deriv_of_analyticOnNhd
    (F : ℂ × A → ℂ) (D : Set (ℂ × A))
    (hD : IsOpen D) (hF : AnalyticOnNhd ℂ F D) :
    ContinuousOn (fun t : ℂ × A =>
      deriv (fun w : ℂ => F (w,t.2)) t.1) D := by
  have hdf : ContinuousOn (fderiv ℂ F) D :=
    (hF.contDiffOn_of_completeSpace (n := 1)).continuousOn_fderiv_of_isOpen
      hD (by norm_num)
  have happly : Continuous (fun L : (ℂ × A →L[ℂ] ℂ) => L (1,0)) := by
    fun_prop
  have hcont : ContinuousOn (fun t : ℂ × A =>
      (fderiv ℂ F t) (1,0)) D := happly.comp_continuousOn hdf
  apply hcont.congr
  intro t ht
  exact (deriv_spectral_section_eq_fderiv F t.1 t.2
    (hF t ht).differentiableAt)

end NLS.ComplexAnalysis
