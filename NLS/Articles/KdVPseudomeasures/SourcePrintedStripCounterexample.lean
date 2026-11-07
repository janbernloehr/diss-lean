import NLS.KdV.SingularHillFreeSpectrum
import Mathlib.Analysis.Real.Pi.Bounds

/-! The printed strip (9) with radius 12n contains the zero free
Fourier eigenvalue when n=1. Its claimed Q_1 inverse in (10) therefore
does not exist. The verified spectral APIs use radius 6n instead. -/
noncomputable section
open Set Complex NLS.KdV NLS.Fourier NLS.Fourier.SmoothPeriodicTest
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

def printedHillStrip (n : ℕ) : Set ℂ := {z | |z.re-freeHillValue n| ≤ 12*(n:ℝ)}

private theorem pi_sq_lt_ten : Real.pi^2 < 10 := by
  have h := mul_pos (sub_pos.mpr Real.pi_lt_d2) (add_pos (by norm_num : (0:ℝ)<3.15) Real.pi_pos)
  nlinarith

theorem zero_mem_printedHillStrip_one : (0:ℂ) ∈ printedHillStrip 1 := by
  have h : |0-Real.pi^2| ≤ 12 := by
    rw [zero_sub,abs_neg,abs_of_nonneg (sq_nonneg _)]
    exact pi_sq_lt_ten.le.trans (by norm_num)
  simpa only [printedHillStrip,mem_ofPred_eq,zero_re,freeHillValue,Int.cast_natCast,
    Nat.cast_one,Int.cast_one,one_pow,mul_one] using h

theorem printedStrip_Q1_free_kernel_counterexample :
    (0:ℂ) ∈ printedHillStrip 1 ∧
      ∃ f : FourierLebesgueSpace (2:ℝ) 1 2, f ≠ 0 ∧
        f.val (mode (-1))=0 ∧ f.val (mode 1)=0 ∧ singularHillOperator 0 f=0 := by
  refine ⟨zero_mem_printedHillStrip_one,singularHillFreeMode 0,
    singularHillFreeMode_ne_zero 0,by simp,by simp,?_⟩
  have h := singularHillFreeMode_eigen 0
  simpa only [freeHillValue,Int.cast_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),
    mul_zero,ofReal_zero,zero_smul] using h

/-- Even away from zero, the free constant-mode reciprocal is unbounded
on the printed first strip. This rules out the uniform bound underlying
Lemma 2.4 on the entire printed n=1 strip. -/
theorem printedStrip_one_inverse_unbounded :
    ¬ ∃ C : ℝ, 1 ≤ C ∧ ∀ z ∈ printedHillStrip 1, z ≠ 0 → ‖z⁻¹‖ ≤ C := by
  rintro ⟨C,hC,hbound⟩
  have hCp : 0 < C := by linarith
  let t : ℝ := 1/(2*C)
  have ht : 0 < t := by dsimp only [t]; positivity
  have ht1 : t ≤ 1 := by
    dsimp only [t]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hz : (t:ℂ) ∈ printedHillStrip 1 := by
    have h : |t-Real.pi^2| ≤ 12 := by
      apply abs_le.mpr
      constructor <;> nlinarith [pi_sq_lt_ten,sq_nonneg Real.pi]
    simpa only [printedHillStrip,mem_ofPred_eq,ofReal_re,freeHillValue,Int.cast_natCast,
      Nat.cast_one,Int.cast_one,one_pow,mul_one] using h
  have hh := hbound (t:ℂ) hz (ofReal_ne_zero.mpr ht.ne')
  have hn : ‖(t:ℂ)⁻¹‖=2*C := by
    rw [norm_inv,Complex.norm_real,Real.norm_of_nonneg ht.le]
    simp only [t,one_div,inv_inv]
  rw [hn] at hh
  linarith

end NLS.Articles.KdVPseudomeasures
