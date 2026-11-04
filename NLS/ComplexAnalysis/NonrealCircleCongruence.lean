import Mathlib.MeasureTheory.Integral.CircleIntegral

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
namespace NLS.ComplexAnalysis

/-- Two functions agreeing off the real axis agree off a finite subset
of each centered positive-radius circle. -/
theorem eventuallyEq_circle_of_eq_nonreal (f g : ℂ → ℂ) (r : ℝ) (hr : 0<r)
    (heq : ∀ E : ℂ, E.im≠0 → f E=g E) :
    f =ᶠ[codiscreteWithin (sphere (0:ℂ) r)] g := by
  have hfin : ({(r:ℂ),(-r:ℂ)} : Set ℂ).Finite := by simp
  filter_upwards [self_mem_codiscreteWithin (sphere (0:ℂ) r),
    compl_finite_mem_codiscreteWithin (s := sphere (0:ℂ) r) hfin] with E hE hnot
  apply heq
  intro hi
  have hEC : E=(E.re : ℂ) := by apply Complex.ext <;> simp [hi]
  have hnorm : |E.re|=r := by
    have hn : ‖E‖=r := by simpa only [mem_sphere_iff_norm,sub_zero] using hE
    rw [hEC,norm_real,Real.norm_eq_abs] at hn
    exact hn
  have hs : E.re=r ∨ E.re=-r := abs_eq_abs.mp (hnorm.trans (abs_of_pos hr).symm)
  apply hnot
  rcases hs with hs | hs
  · exact Or.inl (hEC.trans (congrArg (fun a : ℝ => (a:ℂ)) hs))
  · exact Or.inr (hEC.trans (by simpa only [ofReal_neg] using congrArg (fun a : ℝ => (a:ℂ)) hs))

end NLS.ComplexAnalysis
