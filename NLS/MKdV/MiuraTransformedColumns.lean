import NLS.MKdV.PhysicalMiuraFundamentalMatrix
import NLS.MKdV.MiuraAbsolutelyContinuousEigenfunction

/-! # The actual transformed columns in Lemma 2's proof

The entries are the ZS columns' scalar combinations and their actual
derivatives. Their matrix is the literal product A*M, with determinant
-2*z. The scalar energy is z^2, including the zero-parameter limit.
-/
noncomputable section
open Set Complex Matrix NLS.LinearVolterra NLS.ZakharovShabat
namespace NLS.MKdV

def miuraTransformedColumns (Φ : Curve (ℂ × ℂ)) (z : ℂ) (x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![classicalMiuraSolution Φ z (1,0) x,classicalMiuraSolution Φ z (0,1) x;
     deriv (classicalMiuraSolution Φ z (1,0)) x,deriv (classicalMiuraSolution Φ z (0,1)) x]

theorem miuraTransformedColumns_eq_gauge_mul
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t)) (t : Icc (0:ℝ) 1) :
    miuraTransformedColumns Φ z t = miuraPaperGauge (u t) z*classicalFundamentalMatrix Φ z t := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [miuraTransformedColumns,deriv_classicalMiuraSolution_entries Φ u z _ hΦ t,
      miuraPaperGauge,classicalFundamentalMatrix,classicalMiuraSolution,
      Matrix.mul_apply,Fin.sum_univ_two]

theorem det_miuraTransformedColumns
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t)) (t : Icc (0:ℝ) 1) :
    (miuraTransformedColumns Φ z t).det = -2*z := by
  rw [miuraTransformedColumns_eq_gauge_mul Φ u z hΦ t,Matrix.det_mul,
    det_miuraPaperGauge,det_classicalFundamentalMatrix,mul_one]

theorem isUnit_miuraTransformedColumns_iff
    (Φ : Curve (ℂ × ℂ)) (u : ℝ → ℂ) (z : ℂ)
    (hΦ : ∀ t : Icc (0:ℝ) 1, Φ t = (u t,u t)) (t : Icc (0:ℝ) 1) :
    IsUnit (miuraTransformedColumns Φ z t) ↔ z ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det,det_miuraTransformedColumns Φ u z hΦ t,
    isUnit_iff_ne_zero,mul_ne_zero_iff]
  simp

end NLS.MKdV
