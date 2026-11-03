import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Action-direction derivatives are fixed by one-sided realized data -/
noncomputable section
open Set
namespace NLS.ComplexAnalysis
variable {A X : Type*} [NormedAddCommGroup A] [NormedSpace ℂ A]

theorem fderiv_eq_of_nonnegative_ray_realization (F G : A → ℂ) (p : X → A) (h : X → ℂ)
    (b v : A) (hF : DifferentiableAt ℂ F b) (hG : DifferentiableAt ℂ G b)
    (hrecF : ∀ x, F (p x) = h x) (hrecG : ∀ x, G (p x) = h x)
    (hray : ∀ t : ℝ, 0 ≤ t → ∃ x, p x = b+(t : ℂ) • v) :
    fderiv ℂ F b v = fderiv ℂ G b v := by
  let c : ℝ → A := fun t => b+(t : ℂ) • v
  have hc0 : c 0 = b := by simp [c]
  have hc : HasDerivAt c v 0 := by
    have ht : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := (hasDerivAt_id (0 : ℝ)).ofReal_comp
    simpa only [c,Pi.add_apply,zero_add,one_smul] using! (hasDerivAt_const (0 : ℝ) b).add (ht.smul_const v)
  have hFD : HasFDerivAt F ((fderiv ℂ F b).restrictScalars ℝ) (c 0) := by
    rw [hc0]
    exact hF.hasFDerivAt.restrictScalars ℝ
  have hGD : HasFDerivAt G ((fderiv ℂ G b).restrictScalars ℝ) (c 0) := by
    rw [hc0]
    exact hG.hasFDerivAt.restrictScalars ℝ
  have hDF := hFD.comp_hasDerivAt 0 hc
  have hDG := hGD.comp_hasDerivAt 0 hc
  have he : ∀ t ∈ Ici (0 : ℝ), F (c t) = G (c t) := by
    intro t ht
    obtain ⟨x,hx⟩ := hray t ht
    change F (b+(t : ℂ) • v) = G (b+(t : ℂ) • v)
    rw [← hx,hrecF,hrecG]
  exact UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici 0)
    hDF.hasDerivWithinAt (hDG.hasDerivWithinAt.congr_of_mem he (mem_Ici.mpr le_rfl))

end NLS.ComplexAnalysis
