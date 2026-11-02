import NLS.ComplexAnalysis.AnalyticSquareDescent
import NLS.ComplexAnalysis.CauchyFiniteHoles
import NLS.ComplexAnalysis.RightHalfPlaneSquareRoot

/-! # Dividing an odd entire function and descending to the square

The filled quotient by twice the frequency is an entire function of the
energy, including at the ramification point zero.
-/
noncomputable section
open Set Complex
namespace NLS.ComplexAnalysis

def oddSquareDescent (f : ℂ → ℂ) (lambda : ℂ) : ℂ :=
  dslope f 0 (Complex.sqrt lambda)/2

theorem dslope_zero_even_of_odd (f : ℂ → ℂ) (hodd : ∀ z, f (-z) = -f z) (z : ℂ) :
    dslope f 0 (-z) = dslope f 0 z := by
  by_cases hz : z = 0
  · simp only [hz,neg_zero]
  have hf0 : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linear_combination h/2
  rw [dslope_of_ne f (neg_ne_zero.mpr hz),dslope_of_ne f hz]
  simp only [slope,smul_eq_mul,vsub_eq_sub,hf0,sub_zero,hodd,inv_neg,neg_mul_neg]

theorem oddSquareDescent_sq (f : ℂ → ℂ) (hodd : ∀ z, f (-z) = -f z) (z : ℂ) :
    oddSquareDescent f (z^2) = dslope f 0 z/2 := by
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (sq_sqrt (z^2)) with h | h
  · simp only [oddSquareDescent,h]
  · simp only [oddSquareDescent,h,dslope_zero_even_of_odd f hodd]

theorem oddSquareDescent_factor (f : ℂ → ℂ) (hodd : ∀ z, f (-z) = -f z) (z : ℂ) :
    (2*z)*oddSquareDescent f (z^2) = f z := by
  have hf0 : f 0 = 0 := by have h := hodd 0; simp only [neg_zero] at h; linear_combination h/2
  rw [oddSquareDescent_sq f hodd]
  have he := sub_smul_dslope f 0 z
  simp only [sub_zero,smul_eq_mul,hf0] at he
  linear_combination he

theorem analyticOnNhd_oddSquareDescent (f : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f univ) (hodd : ∀ z, f (-z) = -f z) :
    AnalyticOnNhd ℂ (oddSquareDescent f) univ := by
  have hg := analyticOnNhd_dslope_of_analytic f univ 0 hf (mem_univ _)
  intro lambda _
  have he : (fun z => oddSquareDescent f (z^2)) = (fun z => dslope f 0 z/2) := by
    funext z
    exact oddSquareDescent_sq f hodd z
  have ha : AnalyticAt ℂ (fun z => oddSquareDescent f (z^2)) (Complex.sqrt lambda) := by
    rw [he]
    exact (hg _ (mem_univ _)).div_const
  simpa only [sq_sqrt] using analyticAt_of_comp_sq (oddSquareDescent f) (Complex.sqrt lambda) ha

end NLS.ComplexAnalysis
