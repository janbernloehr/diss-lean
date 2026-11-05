import NLS.ZakharovShabat.ClassicalFundamentalSolution
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Exact zero-frequency monodromy for a continuous equal-component
Dirac source. The trace depends only on the literal unit-interval mean. -/
noncomputable section
open Set Complex MeasureTheory intervalIntegral NLS.LinearVolterra
namespace NLS.ZakharovShabat

def diagonalZeroSolution (f : ℝ → ℂ) (v : ℂ × ℂ) (t : ℝ) : ℂ × ℂ :=
  let P := ∫ s in (0:ℝ)..t, f s
  (cosh P*v.1+I*sinh P*v.2,-I*sinh P*v.1+cosh P*v.2)

theorem hasDerivAt_diagonalZeroSolution (f : ℝ → ℂ) (hf : Continuous f) (v : ℂ × ℂ) (t : ℝ) :
    HasDerivAt (diagonalZeroSolution f v)
      (classicalODECoefficient (f t,f t) 0 (diagonalZeroSolution f v t)) t := by
  have hP := integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
    hf.stronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hC := (Complex.hasDerivAt_cosh (∫ s in (0:ℝ)..t, f s)).comp t hP
  have hS := (Complex.hasDerivAt_sinh (∫ s in (0:ℝ)..t, f s)).comp t hP
  have hd := ((hC.mul_const v.1).add ((hS.const_mul I).mul_const v.2)).prodMk
    (((hS.const_mul (-I)).mul_const v.1).add (hC.mul_const v.2))
  change HasDerivAt (diagonalZeroSolution f v) _ t at hd
  have he : classicalODECoefficient (f t,f t) 0 (diagonalZeroSolution f v t) =
      (sinh (∫ s in (0:ℝ)..t, f s) * f t * v.1 +
        I * (cosh (∫ s in (0:ℝ)..t, f s) * f t) * v.2,
       -I * (cosh (∫ s in (0:ℝ)..t, f s) * f t) * v.1 +
        sinh (∫ s in (0:ℝ)..t, f s) * f t * v.2) := by
    apply Prod.ext <;> simp only [diagonalZeroSolution, classicalODECoefficient_apply] <;>
      ring_nf <;> simp [I_sq]
  rw [he]
  exact hd

theorem classicalSolution_diagonal_zero (Φ : Curve (ℂ × ℂ)) (f : ℝ → ℂ) (hf : Continuous f)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t=(f t,f t)) (v : ℂ × ℂ) (t : Icc (0:ℝ) 1) :
    classicalSolution Φ 0 v t=diagonalZeroSolution f v t := by
  have h := classicalSolution_unique Φ 0 v (diagonalZeroSolution f v)
    (fun x _ => (hasDerivAt_diagonalZeroSolution f hf v x).continuousAt.continuousWithinAt)
    (by simp [diagonalZeroSolution]) (fun x _ => by
      rw [hΦ x]
      exact hasDerivAt_diagonalZeroSolution f hf v x)
  exact (h t.property).symm

theorem classicalDiscriminant_diagonal_zero (Φ : Curve (ℂ × ℂ)) (f : ℝ → ℂ) (hf : Continuous f)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t=(f t,f t)) :
    classicalDiscriminant Φ 0=2*cosh (∫ s in (0:ℝ)..1, f s) := by
  have h₁ := classicalSolution_diagonal_zero Φ f hf hΦ (1,0) ⟨1,by norm_num⟩
  have h₂ := classicalSolution_diagonal_zero Φ f hf hΦ (0,1) ⟨1,by norm_num⟩
  simp only [classicalDiscriminant,classicalMonodromy,classicalFundamentalMatrix,
    Matrix.trace_fin_two,Matrix.of_apply,Matrix.cons_val_zero,Matrix.cons_val_one]
  rw [h₁,h₂]
  simp [diagonalZeroSolution,two_mul]

end NLS.ZakharovShabat
