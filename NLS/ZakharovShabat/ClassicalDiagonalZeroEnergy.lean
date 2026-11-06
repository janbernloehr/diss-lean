import NLS.ZakharovShabat.ClassicalFreeDiscriminant
import NLS.FunctionalAnalysis.UnitIntervalMean
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! # The physical diagonal monodromy at zero energy

An arbitrary continuous complex profile has an explicit hyperbolic
fundamental solution. Its trace is twice the hyperbolic cosine of the
literal unit-interval mean, with no regularity or reality restriction.
-/
noncomputable section
open Set Complex NLS.LinearVolterra
namespace NLS.ZakharovShabat

private def cumulative (u : Curve ℂ) (x : ℝ) : ℂ := ∫ s in (0 : ℝ)..x, extend u s

private theorem cumulative_hasDerivAt (u : Curve ℂ) (x : ℝ) :
    HasDerivAt (cumulative u) (extend u x) x := by
  have hc := continuous_extend u
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

/-- The actual ZS initial-value solution at zero frequency for diagonal
continuous potentials, expressed through its physical integral. -/
theorem classicalSolution_diagonal_zero_of_curve (u : Curve ℂ) (φ : Curve (ℂ × ℂ))
    (hφ : ∀ t, φ t = (u t,u t)) (v : ℂ × ℂ) (t : Icc (0 : ℝ) 1) :
    classicalSolution φ 0 v t =
      (cosh (∫ s in (0 : ℝ)..t.val, extend u s)*v.1+
        I*sinh (∫ s in (0 : ℝ)..t.val, extend u s)*v.2,
       -I*sinh (∫ s in (0 : ℝ)..t.val, extend u s)*v.1+
        cosh (∫ s in (0 : ℝ)..t.val, extend u s)*v.2) := by
  let f : ℝ → ℂ × ℂ := fun x =>
    (cosh (cumulative u x)*v.1+I*sinh (cumulative u x)*v.2,
     -I*sinh (cumulative u x)*v.1+cosh (cumulative u x)*v.2)
  have hc : Continuous (cumulative u) := continuous_iff_continuousAt.mpr
    (fun x => (cumulative_hasDerivAt u x).continuousAt)
  have hf : Continuous f := by
    exact ((Complex.continuous_cosh.comp hc).mul continuous_const |>.add
      ((continuous_const.mul (Complex.continuous_sinh.comp hc)).mul continuous_const)).prodMk
        (((continuous_const.mul (Complex.continuous_sinh.comp hc)).mul continuous_const).add
          ((Complex.continuous_cosh.comp hc).mul continuous_const))
  have he := classicalSolution_unique φ 0 v f hf.continuousOn
    (by simp [f,cumulative]) (by
      intro s _
      have hd := cumulative_hasDerivAt u s
      rw [extend_coe] at hd
      have hC : HasDerivAt (fun x => cosh (cumulative u x))
          (sinh (cumulative u s)*(u s)) s := by
        simpa [mul_comm] using! ((Complex.hasDerivAt_cosh (cumulative u s)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s.val hd
      have hS : HasDerivAt (fun x => sinh (cumulative u x))
          (cosh (cumulative u s)*(u s)) s := by
        simpa [mul_comm] using! ((Complex.hasDerivAt_sinh (cumulative u s)).hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt s.val hd
      have h := ((hC.mul_const v.1).add ((hS.const_mul I).mul_const v.2)).prodMk
        (((hS.const_mul (-I)).mul_const v.1).add (hC.mul_const v.2))
      convert! h using 1
      rw [hφ s]
      simp only [f,classicalODECoefficient_apply,mul_zero,zero_mul,zero_add,add_zero]
      apply Prod.ext <;> dsimp <;> ring_nf <;> simp only [I_sq] <;> ring)
  exact (he t.property).symm

/-- The physical monodromy trace, not a formal spectral surrogate. -/
theorem classicalDiscriminant_diagonal_zero_of_curve (u : Curve ℂ) (φ : Curve (ℂ × ℂ))
    (hφ : ∀ t, φ t = (u t,u t)) :
    classicalDiscriminant φ 0 = 2*cosh (unitIntervalMean u) := by
  change (classicalFundamentalMatrix φ 0 1).trace = _
  have h1 := classicalSolution_diagonal_zero_of_curve u φ hφ (1,0) ⟨1,by constructor <;> norm_num⟩
  have h2 := classicalSolution_diagonal_zero_of_curve u φ hφ (0,1) ⟨1,by constructor <;> norm_num⟩
  simp only [classicalFundamentalMatrix,Matrix.trace_fin_two_of]
  rw [h1,h2]
  simp only [unitIntervalMean_apply,mul_one,mul_zero,add_zero,zero_add]
  ring

end NLS.ZakharovShabat
