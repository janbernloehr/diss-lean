import NLS.ZakharovShabat.OrderedDyadicSource
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Quantitative cost of the ordered dyadic spectral normalization -/
noncomputable section
open Complex NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The normalization at an imaginary parameter is a quotient of real interactions. -/
theorem norm_orderedDyadicNormalization (P : ℕ) (hP : 3 ≤ P) :
    ‖orderedPeriodicNormalization (orderedDyadicCurve (2*P)) (I*(2^P : ℝ))‖ =
      (Real.exp (2^P)-1)^2 /
        (dyadicUpperInteraction (2*P) (2^P)*dyadicLowerInteraction (2*P) (2^P)) := by
  rw [norm_orderedPeriodicNormalization]
  obtain ⟨hu,hv⟩ := orderedDyadicCurve_interactions (2*P) (2^P)
  rw [hu,hv,show -I*(I*(2^P : ℝ)) = ((2^P : ℝ) : ℂ) by ring_nf; simp [I_sq],
    ← Complex.ofReal_exp, ← ofReal_one, ← ofReal_sub]
  simp only [norm_mul,norm_neg,norm_I,one_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_pos (dyadicUpperInteraction_pow_pos P hP),
    abs_of_pos (dyadicLowerInteraction_pos (2*P) (by omega) (2^P) (by positivity)),sq_abs]

/-- The final tent is so narrow that the exponential loss is at most e. -/
theorem dyadic_height_width_le_one (P : ℕ) (hP : 1 ≤ P) :
    2*(2 : ℝ)^P*dyadicTentWidth (2*P) ≤ 1 := by
  have he : (2 : ℝ)^P*dyadicTentWidth (2*P) = (1/2 : ℝ)^P := by
    unfold dyadicTentWidth
    rw [pow_mul,← mul_pow]
    norm_num
  rw [mul_assoc,he]
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1/2)
    (by norm_num : (1/2 : ℝ) ≤ 1) hP
  norm_num at h
  linarith

/-- The exact normalization has size O(1/P), with an explicit constant. -/
theorem norm_orderedDyadicNormalization_le (P : ℕ) (hP : 3 ≤ P) :
    ‖orderedPeriodicNormalization (orderedDyadicCurve (2*P)) (I*(2^P : ℝ))‖ ≤
      12/(P-2 : ℕ) := by
  let H : ℝ := 2^P
  let A := dyadicUpperInteraction (2*P) H
  let B := dyadicLowerInteraction (2*P) H
  let D : ℝ := (P-2 : ℕ)
  have hD : 0 < D := by dsimp [D]; exact_mod_cast (show 0 < P-2 by omega)
  have hA : 0 < A := dyadicUpperInteraction_pow_pos P hP
  have hB : 0 < B := dyadicLowerInteraction_pos (2*P) (by omega) H (by dsimp [H]; positivity)
  have hAlower : D/4 ≤ A := integral_dyadicTentSum_pow_height P hP
  have hBlower : Real.exp (2*H*(1-dyadicTentWidth (2*P))) ≤ B :=
    integral_lowerDyadicTent_exp_lower (2*P) (by omega) H (by dsimp [H]; positivity)
  have he : Real.exp (2*H*dyadicTentWidth (2*P)) ≤ 3 := by
    apply (Real.exp_le_exp.mpr (dyadic_height_width_le_one P (by omega))).trans
    exact Real.exp_one_lt_three.le
  have hnum : (Real.exp H-1)^2 ≤ Real.exp (2*H) := by
    rw [show 2*H = H+H by ring,Real.exp_add]
    have hh : 1 ≤ Real.exp H := Real.one_le_exp (by dsimp [H]; positivity)
    nlinarith
  have hexp : Real.exp (2*H) ≤ 3*B := by
    calc
      _ = Real.exp (2*H*dyadicTentWidth (2*P))*Real.exp (2*H*(1-dyadicTentWidth (2*P))) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ 3*Real.exp (2*H*(1-dyadicTentWidth (2*P))) :=
        mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
      _ ≤ 3*B := mul_le_mul_of_nonneg_left hBlower (by norm_num)
  rw [norm_orderedDyadicNormalization P hP]
  change (Real.exp H-1)^2/(A*B) ≤ 12/D
  apply (div_le_iff₀ (mul_pos hA hB)).mpr
  have hratio : 3 ≤ (12/D)*A := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hD).mpr
    linarith
  calc
    _ ≤ 3*B := hnum.trans hexp
    _ ≤ ((12/D)*A)*B := mul_le_mul_of_nonneg_right hratio hB.le
    _ = _ := by ring

end NLS.ZakharovShabat
