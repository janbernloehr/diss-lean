import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology MeasureTheory
open scoped ENNReal ComplexConjugate Classical

namespace NLS.ComplexAnalysis



private theorem real_sphere_point (c r : ℝ) (z : ℂ) (hz : z∈sphere (c : ℂ) r) (him : z.im=0) :
    z=(c+r : ℝ) ∨ z=(c-r : ℝ) := by
  have he : z=(z.re : ℂ) := by apply Complex.ext <;> simp [him]
  have hd : |z.re-c|=r := by
    rw [mem_sphere,dist_eq_norm,he,← ofReal_sub,norm_real,Real.norm_eq_abs] at hz
    exact hz
  by_cases hsign : 0≤z.re-c
  · rw [abs_of_nonneg hsign] at hd
    left
    rw [he]
    congr 1
    linarith
  · rw [abs_of_neg (lt_of_not_ge hsign)] at hd
    right
    rw [he]
    congr 1
    linarith

/-- Agreement off the real axis determines a real-centered circle
integral; the two real crossings have zero angular measure. -/
theorem circleIntegral_eq_of_eq_on_nonreal
    (f g : ℂ → ℂ) (c r : ℝ) (hr : 0<r)
    (he : ∀ z∈sphere (c : ℂ) r, z.im≠0 → f z=g z) :
    (∮ z in C((c : ℂ),r),f z)=∮ z in C((c : ℂ),r),g z := by
  apply circleIntegral.circleIntegral_congr_codiscreteWithin _ hr.ne'
  rw [abs_of_pos hr]
  have hfinite : ({((c+r : ℝ) : ℂ),((c-r : ℝ) : ℂ)} : Set ℂ).Finite :=
    (finite_singleton _).insert _
  filter_upwards [compl_finite_mem_codiscreteWithin hfinite,self_mem_codiscreteWithin (sphere (c : ℂ) r)] with z hz hzs
  apply he z hzs
  intro him
  rcases real_sphere_point c r z hzs him with hh | hh
  · exact hz (by simp only [mem_insert_iff,mem_singleton_iff,hh,true_or])
  · exact hz (by simp only [mem_insert_iff,mem_singleton_iff,hh,or_true])

end NLS.ComplexAnalysis
