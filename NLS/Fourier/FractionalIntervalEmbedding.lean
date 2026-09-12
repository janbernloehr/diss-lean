import NLS.Fourier.FractionalBoundaryKernel

/-!
# Lowering the intrinsic fractional regularity on a bounded interval

The diameter gives an explicit energy bound. In particular, finite intrinsic
half-regularity energy implies every smaller positive regularity, without
requiring any endpoint matching or exterior energy at the critical index.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Kernel comparison on an interval, including its diagonal. -/
theorem fractionalDistanceKernel_le_of_regularity {t s L x y : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hL : 0 < L)
    (hx : x ∈ Ioo 0 L) (hy : y ∈ Ioo 0 L) :
    fractionalDistanceKernel t x y ≤
      ENNReal.ofReal (L ^ (2 * (s - t))) * fractionalDistanceKernel s x y := by
  by_cases he : x = y
  · subst y
    simp only [fractionalDistanceKernel, sub_self, abs_zero,
      Real.zero_rpow (by linarith : -(1 + 2 * t) ≠ 0), ENNReal.ofReal_zero, zero_le]
  · have hd : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr he)
    have hdL : |x - y| ≤ L := (abs_le).mpr ⟨by linarith [hx.1, hy.2], by linarith [hx.2, hy.1]⟩
    have hp : |x - y| ^ (-(1 + 2 * t)) =
        |x - y| ^ (2 * (s - t)) * |x - y| ^ (-(1 + 2 * s)) := by
      rw [← Real.rpow_add hd]
      congr 1
      ring
    unfold fractionalDistanceKernel
    rw [hp, ← ENNReal.ofReal_mul (Real.rpow_nonneg hL.le _)]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hd.le hdL (by linarith))
      (Real.rpow_nonneg hd.le _)

/-- Explicit loss when lowering fractional regularity on a bounded interval. -/
theorem fractionalIntervalEnergy_le_of_regularity {t s L : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hL : 0 < L) (f : ℝ → ℂ) :
    fractionalIntervalEnergy t L f ≤
      ENNReal.ofReal (L ^ (2 * (s - t))) * fractionalIntervalEnergy s L f := by
  unfold fractionalIntervalEnergy
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro x hx
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_mono' measurableSet_Ioo
  intro y hy
  simpa only [mul_left_comm] using mul_le_mul' (le_refl (ENNReal.ofReal (‖f x - f y‖ ^ 2)))
    (fractionalDistanceKernel_le_of_regularity ht hts hL hx hy)

/-- Finiteness descends to every smaller nonnegative fractional regularity. -/
theorem fractionalIntervalEnergy_lt_top_of_regularity {t s L : ℝ}
    (ht : 0 ≤ t) (hts : t ≤ s) (hL : 0 < L) (f : ℝ → ℂ)
    (hE : fractionalIntervalEnergy s L f < ⊤) : fractionalIntervalEnergy t L f < ⊤ :=
  (fractionalIntervalEnergy_le_of_regularity ht hts hL f).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hE)

end NLS.Fourier
