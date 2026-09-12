import NLS.Fourier.IntervalDilation

/-!
# Exact scaling of intrinsic fractional interval energy

The two Jacobians and the distance kernel give the factor `c^(2s-1)`.
These identities include infinite energies and use no regularity assumption
on the physical representative.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The distance kernel has its exact homogeneity, including the diagonal. -/
theorem fractionalDistanceKernel_dilation {c : ℝ} (hc : 0 < c) (s x y : ℝ) :
    fractionalDistanceKernel s x y =
      ENNReal.ofReal (c ^ (1 + 2 * s)) * fractionalDistanceKernel s (c * x) (c * y) := by
  unfold fractionalDistanceKernel
  rw [← mul_sub, abs_mul, abs_of_pos hc, Real.mul_rpow hc.le (abs_nonneg _),
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _)]
  congr 1
  rw [← mul_assoc, ← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero, one_mul]

private theorem dilation_power_factor {c : ℝ} (hc : 0 < c) (s : ℝ) :
    ENNReal.ofReal (c ^ (1 + 2 * s)) * ENNReal.ofReal c⁻¹ * ENNReal.ofReal c⁻¹ =
      ENNReal.ofReal (c ^ (2 * s - 1)) := by
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hc.le _),
    ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hc.le _) (inv_nonneg.mpr hc.le))]
  congr 1
  rw [← Real.rpow_neg_one c, ← Real.rpow_add hc, ← Real.rpow_add hc]
  congr 1
  ring

/-- Exact fractional-energy scaling under a positive dilation. -/
theorem fractionalIntervalEnergy_dilation {c : ℝ} (hc : 0 < c) (s L : ℝ) (f : ℝ → ℂ) :
    fractionalIntervalEnergy s L (intervalDilation c f) =
      ENNReal.ofReal (c ^ (2 * s - 1)) * fractionalIntervalEnergy s (c * L) f := by
  let G := fun x y : ℝ => ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalDistanceKernel s x y
  calc
    _ = ENNReal.ofReal (c ^ (1 + 2 * s)) *
        ∫⁻ x : ℝ in Ioo 0 L, ∫⁻ y : ℝ in Ioo 0 L, G (c * x) (c * y) := by
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro x
      rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      apply lintegral_congr
      intro y
      change ENNReal.ofReal (‖f (c * x) - f (c * y)‖ ^ 2) * fractionalDistanceKernel s x y = _
      rw [fractionalDistanceKernel_dilation hc s x y]
      simp only [G, mul_left_comm]
    _ = ENNReal.ofReal (c ^ (1 + 2 * s)) *
        (ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c⁻¹ * fractionalIntervalEnergy s (c * L) f)) := by
      congr 1
      calc
        _ = ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal c⁻¹ * ∫⁻ y : ℝ in Ioo 0 (c * L), G (c * x) y := by
          apply lintegral_congr
          intro x
          exact lintegral_interval_dilation hc L (G (c * x))
        _ = ENNReal.ofReal c⁻¹ * (ENNReal.ofReal c⁻¹ * fractionalIntervalEnergy s (c * L) f) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
            lintegral_interval_dilation hc L (fun x => ∫⁻ y : ℝ in Ioo 0 (c * L), G x y)]
          rfl
    _ = _ := by rw [← mul_assoc, ← mul_assoc, dilation_power_factor hc s]

/-- The two inhomogeneous terms have different exact dilation factors. -/
theorem intrinsicIntervalEnergy_dilation {c : ℝ} (hc : 0 < c) (s L : ℝ) (f : ℝ → ℂ) :
    intrinsicIntervalEnergy s L (intervalDilation c f) =
      ENNReal.ofReal c⁻¹ * intervalSquareEnergy (c * L) f +
        ENNReal.ofReal (c ^ (2 * s - 1)) * fractionalIntervalEnergy s (c * L) f := by
  rw [intrinsicIntervalEnergy, intervalSquareEnergy_dilation hc, fractionalIntervalEnergy_dilation hc]

/-- A finite uniform factor controlling both intrinsic energy terms under dilation. -/
def intrinsicDilationConstant (s c : ℝ) : ℝ≥0∞ := ENNReal.ofReal c⁻¹ + ENNReal.ofReal (c ^ (2 * s - 1))

theorem intrinsicDilationConstant_lt_top (s c : ℝ) : intrinsicDilationConstant s c < ⊤ :=
  ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩

theorem intrinsicIntervalEnergy_dilation_le {c : ℝ} (hc : 0 < c) (s L : ℝ) (f : ℝ → ℂ) :
    intrinsicIntervalEnergy s L (intervalDilation c f) ≤
      intrinsicDilationConstant s c * intrinsicIntervalEnergy s (c * L) f := by
  rw [intrinsicIntervalEnergy_dilation hc, intrinsicIntervalEnergy, mul_add]
  exact add_le_add (mul_le_mul' (le_add_right le_rfl) le_rfl)
    (mul_le_mul' (le_add_left le_rfl) le_rfl)

/-- Finite intrinsic data gives a quantitative real size bound after dilation. -/
theorem intrinsicIntervalSize_dilation_le {c : ℝ} (hc : 0 < c) (s L : ℝ) (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 (c * L))))
    (hE : fractionalIntervalEnergy s (c * L) f < ⊤) :
    intrinsicIntervalSize s L (intervalDilation c f) ≤
      Real.sqrt (intrinsicDilationConstant s c).toReal * intrinsicIntervalSize s (c * L) f := by
  have hI := intrinsicIntervalEnergy_lt_top f hf hE
  have hb := intrinsicIntervalEnergy_dilation_le hc s L f
  have hJ := hb.trans_lt (ENNReal.mul_lt_top (intrinsicDilationConstant_lt_top s c) hI)
  have hh : ENNReal.ofReal (‖intrinsicIntervalSize s L (intervalDilation c f)‖ ^ 2) ≤
      intrinsicDilationConstant s c * intrinsicIntervalEnergy s (c * L) f := by
    rw [Real.norm_of_nonneg (intrinsicIntervalSize_nonneg _ _ _), intrinsicIntervalSize_sq,
      ENNReal.ofReal_toReal hJ.ne]
    exact hb
  simpa only [Real.norm_of_nonneg (intrinsicIntervalSize_nonneg _ _ _)] using!
    norm_le_sqrt_energy (intrinsicIntervalSize s L (intervalDilation c f))
      (intrinsicDilationConstant_lt_top s c) hI hh

end NLS.Fourier
