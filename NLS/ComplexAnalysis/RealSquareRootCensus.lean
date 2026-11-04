import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Multiset.Count
import Mathlib.Tactic

/-! # Exact opposite-square-root counts, including zero ramification, and real-energy square-root coordinate bounds. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis
theorem count_opposite_square_root_pair (r z : ℂ) :
    ({r,-r} : Multiset ℂ).count z = (if z = 0 then 2 else 1)*(if r^2 = z^2 then 1 else 0) := by
  classical
  by_cases hr : r = z
  · subst r
    by_cases hz : z = 0
    · subst z; simp
    · have hneg : -z ≠ z := by intro he; apply hz; linear_combination -(1/2 : ℂ)*he
      simp [hz,Ne.symm hneg]
  · by_cases hn : -r = z
    · have hz : z ≠ 0 := by
        intro hz
        apply hr
        rw [hz] at hn
        exact (neg_eq_zero.mp hn).trans hz.symm
      have hs : r^2 = z^2 := by rw [← hn,neg_sq]
      simp [hr,hn,hz,hs]
    · have hs : r^2 ≠ z^2 := by
        intro he
        have hp : (r-z)*(r+z) = 0 := by linear_combination he
        rcases mul_eq_zero.mp hp with hm | hp
        · exact hr (sub_eq_zero.mp hm)
        · apply hn
          linear_combination -hp
      simp [Ne.symm hr,Ne.symm hn,hs]

theorem square_root_real_coordinate_bounds (w : ℂ) (x A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hw : w^2 = (x : ℂ)) (hlo : -B^2 < x) (hup : x < A^2) : |w.re| < A ∧ |w.im| < B := by
  have hre := congrArg Complex.re hw
  have him := congrArg Complex.im hw
  simp only [pow_two,mul_re,mul_im,ofReal_re,ofReal_im] at hre him
  have hz : w.re = 0 ∨ w.im = 0 := mul_eq_zero.mp (by nlinarith : w.re*w.im = 0)
  rcases hz with hz | hz
  · constructor
    · simpa only [hz,abs_zero] using hA
    · have hs : |w.im|^2 < B^2 := by rw [sq_abs]; nlinarith
      exact (sq_lt_sq₀ (abs_nonneg _) hB.le).mp hs
  · constructor
    · have hs : |w.re|^2 < A^2 := by rw [sq_abs]; nlinarith
      exact (sq_lt_sq₀ (abs_nonneg _) hA.le).mp hs
    · simpa only [hz,abs_zero] using hB

end NLS.ComplexAnalysis
