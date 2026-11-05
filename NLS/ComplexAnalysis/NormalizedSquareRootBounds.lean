import NLS.ComplexAnalysis.PrescribedAnalyticSquareRoot

/-! # Analytic unit roots quantitatively close to a prescribed constant

The principal normalized root has nonnegative real part, so its distance
from one is at most the distance of its square from one. This gives a
local analytic root and a uniform two-sided normalization from any
strict unit-disc bound, without entire-function assumptions.
-/
noncomputable section
set_option autoImplicit false
open Set Metric Complex
namespace NLS.ComplexAnalysis

theorem norm_sqrt_sub_one_le (z : ℂ) : ‖Complex.sqrt z-1‖ ≤ ‖z-1‖ := by
  have hre : 0 ≤ (Complex.sqrt z).re := by rw [Complex.sqrt,cpow_inv_two_re]; positivity
  have hsum : 1 ≤ ‖Complex.sqrt z+1‖ := by
    have hh := re_le_norm (Complex.sqrt z+1)
    simp only [add_re,one_re] at hh
    linarith
  have hs : (Complex.sqrt z)^2 = z := by
    have hh := Complex.cpow_nat_inv_pow z (Nat.succ_ne_zero 1)
    norm_num at hh
    simpa only [Complex.sqrt,one_div] using hh
  have he : (Complex.sqrt z-1)*(Complex.sqrt z+1) = z-1 := by linear_combination hs
  calc
    _ ≤ ‖Complex.sqrt z-1‖*‖Complex.sqrt z+1‖ := by nlinarith [norm_nonneg (Complex.sqrt z-1)]
    _ = ‖z-1‖ := by rw [← norm_mul,he]

theorem prescribedSquareRoot_analytic_and_close
    (f : ℂ → ℂ) (U : Set ℂ) (w : ℂ) (epsilon : ℝ)
    (hf : AnalyticOnNhd ℂ f U) (hw : w ≠ 0) (hepsilon : epsilon < 1)
    (hbound : ∀ z ∈ U, ‖f z/w^2-1‖ ≤ epsilon) :
    AnalyticOnNhd ℂ (prescribedSquareRoot f w) U ∧
      ∀ z ∈ U, prescribedSquareRoot f w z ≠ 0 ∧
        prescribedSquareRoot f w z^2 = f z ∧
        ‖prescribedSquareRoot f w z-w‖ ≤ ‖w‖*epsilon := by
  have hslit (z : ℂ) (hz : z ∈ U) : f z/w^2 ∈ slitPlane := by
    have hh := (abs_re_le_norm (f z/w^2-1)).trans (hbound z hz)
    simp only [sub_re,one_re] at hh
    have hre : 0 < (f z/w^2).re := by linarith [(abs_le.mp hh).1]
    exact mem_slitPlane_iff.mpr (Or.inl hre)
  refine ⟨?_,?_⟩
  · intro z hz
    have hg : AnalyticAt ℂ (fun z => f z/w^2) z := (hf z hz).div_const
    have hs : AnalyticAt ℂ Complex.sqrt (f z/w^2) :=
      Complex.differentiableOn_sqrt.analyticAt (Complex.isOpen_slitPlane.mem_nhds (hslit z hz))
    exact analyticAt_const.mul (hs.comp (f := fun z => f z/w^2) hg)
  · intro z hz
    refine ⟨prescribedSquareRoot_ne_zero f w hw z (hslit z hz),prescribedSquareRoot_sq f w hw z,?_⟩
    rw [prescribedSquareRoot,show w*Complex.sqrt (f z/w^2)-w = w*(Complex.sqrt (f z/w^2)-1) by ring,norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_sqrt_sub_one_le _).trans (hbound z hz)) (norm_nonneg _)

end NLS.ComplexAnalysis
