import NLS.ZakharovShabat.ClassicalFundamentalSolution
import Mathlib.Analysis.ODE.Gronwall

/-!
# Gronwall growth bounds for the actual classical solution

The pair supremum norm gives coefficient bound `|z| + ‖Φ‖`. A real phase
rotation will subsequently remove the real spectral part from this bound.
-/

noncomputable section
open Set Complex
open NLS.LinearVolterra
namespace NLS.ZakharovShabat

theorem norm_classicalODECoefficient_apply_le (φ : ℂ × ℂ) (z : ℂ) (v : ℂ × ℂ) :
    ‖classicalODECoefficient φ z v‖ ≤ (‖z‖ + ‖φ‖) * ‖v‖ := by
  rw [classicalODECoefficient_apply]
  apply norm_prod_le_iff.mpr
  constructor
  · calc
      _ ≤ ‖-I*z*v.1‖ + ‖I*φ.1*v.2‖ := norm_add_le _ _
      _ = ‖z‖ * ‖v.1‖ + ‖φ.1‖ * ‖v.2‖ := by simp only [norm_mul, norm_neg, norm_I, one_mul]
      _ ≤ ‖z‖ * ‖v‖ + ‖φ‖ * ‖v‖ := add_le_add
        (mul_le_mul_of_nonneg_left (norm_fst_le v) (norm_nonneg _))
        (mul_le_mul (norm_fst_le φ) (norm_snd_le v) (norm_nonneg _) (norm_nonneg _))
      _ = _ := by ring
  · calc
      _ ≤ ‖-I*φ.2*v.1‖ + ‖I*z*v.2‖ := norm_add_le _ _
      _ = ‖φ.2‖ * ‖v.1‖ + ‖z‖ * ‖v.2‖ := by simp only [norm_mul, norm_neg, norm_I, one_mul]
      _ ≤ ‖φ‖ * ‖v‖ + ‖z‖ * ‖v‖ := add_le_add
        (mul_le_mul (norm_snd_le φ) (norm_fst_le v) (norm_nonneg _) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_snd_le v) (norm_nonneg _))
      _ = _ := by ring

/-- The solution grows at most exponentially in the spectral and potential norms. -/
theorem norm_classicalSolution_le_exp_norm (φ : Curve (ℂ × ℂ)) (z : ℂ) (v : ℂ × ℂ)
    (t : Icc (0 : ℝ) 1) :
    ‖classicalSolution φ z v t‖ ≤ ‖v‖ * Real.exp ((‖z‖ + ‖φ‖) * t.val) := by
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    (f := classicalSolution φ z v)
    (f' := fun s => classicalODECoefficient (NLS.LinearVolterra.extend φ s) z (classicalSolution φ z v s))
    (δ := ‖v‖) (K := ‖z‖+‖φ‖) (ε := 0) (a := 0) (b := 1)
    (continuous_classicalSolution φ z v).continuousOn (by
      intro s hs
      have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
      simpa only [NLS.LinearVolterra.extend, projIcc_of_mem _ hs'] using
        (hasDerivAt_classicalSolution φ z v ⟨s, hs'⟩).hasDerivWithinAt)
    (by simp only [classicalSolution_zero, le_refl]) (by
      intro s hs
      rw [add_zero]
      exact (norm_classicalODECoefficient_apply_le _ _ _).trans
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (φ.norm_coe_le_norm _)) (norm_nonneg _)))
    t.val t.property
  simpa only [gronwallBound_ε0, sub_zero] using h

end NLS.ZakharovShabat
