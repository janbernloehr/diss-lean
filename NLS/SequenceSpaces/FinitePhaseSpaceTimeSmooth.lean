import NLS.SequenceSpaces.FourierRealPhaseFlow
import NLS.SequenceSpaces.SignedSobolevRealScale
import NLS.SequenceSpaces.WeightedSingle
import NLS.SequenceSpaces.WeightedFiniteCoefficients
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! Joint space-time smoothness of finite native phase rotations.
Finite support removes any growth restriction on the time frequencies;
the physical spatial phase retains its exact unit-period normalization. -/
noncomputable section
open Complex
open scoped ContDiff ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

theorem contDiff_finite_phase_space_time (w : Weight) (hw : ∀ k, w (-k) = w k)
    (freq : ℤ → ℝ) (hf : ∀ k, freq (-k) = -freq k)
    (a : fourierRealZeroSubmodule w p) (S : Finset ℤ)
    (ha : ∀ k ∉ S, a.val.val.val k = 0) :
    ContDiff ℝ ∞ (fun u : ℝ × ℝ => fourierRealZeroSpatialTranslation w hw u.2
      (fourierRealZeroPhaseFlow w freq hf u.1 a)) := by
  let H : ℝ × ℝ → WeightedCoeff w p := fun u => ∑ k ∈ S,
    (exp (((u.2 * (2 * Real.pi * k) : ℝ) : ℂ) * I) *
      exp (((u.1 * freq k : ℝ) : ℂ) * I)) • single w k (a.val.val.val k)
  have hH : ContDiff ℝ ∞ H := by
    apply ContDiff.sum
    intro k _
    have hscalar : ContDiff ℝ ∞ (fun u : ℝ × ℝ =>
        exp (((u.2 * (2 * Real.pi * k) : ℝ) : ℂ) * I) *
          exp (((u.1 * freq k : ℝ) : ℂ) * I)) := by
      have hR : ContDiff ℝ ∞ (fun r : ℝ => (r : ℂ)) := ofRealCLM.contDiff
      fun_prop
    exact hscalar.smul_const (single (p := p) w k (a.val.val.val k))
  have he (u : ℝ × ℝ) : H u =
      (fourierRealZeroSpatialTranslation w hw u.2
        (fourierRealZeroPhaseFlow w freq hf u.1 a)).val.val := by
    apply Subtype.ext
    funext j
    have hsum := map_sum (evalCLM w p j) (fun k : ℤ =>
      (exp (((u.2 * (2 * Real.pi * k) : ℝ) : ℂ) * I) *
        exp (((u.1 * freq k : ℝ) : ℂ) * I)) • single w k (a.val.val.val k)) S
    change (evalCLM w p j) (H u) = _
    rw [hsum, fourierRealZeroSpatialTranslation_apply, fourierRealZeroPhaseFlow_apply]
    simp only [map_smul, evalCLM_apply, single_val, smul_eq_mul]
    by_cases hj : j ∈ S
    · rw [Finset.sum_eq_single j (by intro k _ hkj; simp [hkj.symm])
        (by simp [hj]), Pi.single_eq_same]
      ring
    · rw [ha j hj]
      simp only [mul_zero]
      apply Finset.sum_eq_zero
      intro k hk
      have hkj : j ≠ k := by intro h; exact hj (h ▸ hk)
      simp only [Pi.single_eq_of_ne hkj, mul_zero]
  have hP : ContDiff ℝ ∞ (fourierRealZeroFullProjection (p := p) w hw) :=
    ContinuousLinearMap.contDiff (F := fourierRealZeroSubmodule w p) _
  have h := hP.comp hH
  have hp (u : ℝ × ℝ) : fourierRealZeroFullProjection (p := p) w hw (H u) =
      fourierRealZeroSpatialTranslation w hw u.2
        (fourierRealZeroPhaseFlow w freq hf u.1 a) := by
    rw [he, fourierRealZeroFullProjection_inclusion]
  simpa only [Function.comp_def, hp] using! h

end NLS.WeightedCoeff
