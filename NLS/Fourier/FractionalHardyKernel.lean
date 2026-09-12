import NLS.Fourier.FractionalBoundaryWeight

/-!
# The averaging kernel for the fractional Hardy estimate

Averaging over `x<y<2x` produces the exact coefficient
`(2^(2s)-1)/(2s)`, strictly between zero and one for `0<s<1/2`.
The annular kernel integral and the local difference estimate are the inputs
for absorbing the endpoint-weighted energy.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The coefficient arising when the triangular averaging integral is reversed. -/
def hardyAveragingConstant (s : ℝ) : ℝ := ((2 : ℝ) ^ (2 * s) - 1) / (2 * s)

/-- Integral representation makes the contraction threshold explicit. -/
theorem hardyAveragingConstant_eq_integral {s : ℝ} (hs : 0 < s) :
    hardyAveragingConstant s = ∫ t in (1 : ℝ)..2, t ^ (2 * s - 1) := by
  rw [integral_rpow (Or.inl (by linarith : -1 < 2 * s - 1))]
  simp only [sub_add_cancel, Real.one_rpow, hardyAveragingConstant]

theorem hardyAveragingConstant_pos {s : ℝ} (hs : 0 < s) : 0 < hardyAveragingConstant s := by
  rw [hardyAveragingConstant_eq_integral hs]
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegral.intervalIntegrable_rpow' (by linarith : -1 < 2 * s - 1))
  · intro t ht
    exact Real.rpow_pos_of_pos (by linarith [ht.1]) _
  · norm_num

/-- Exactly the subcritical range permits absorption of the averaged boundary energy. -/
theorem hardyAveragingConstant_lt_one {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) :
    hardyAveragingConstant s < 1 := by
  rw [hardyAveragingConstant_eq_integral hs]
  have hc : ContinuousOn (fun t : ℝ => t ^ (2 * s - 1)) (Icc 1 2) := by
    apply continuousOn_id.rpow_const
    intro t ht
    left
    change t ≠ 0
    linarith [ht.1]
  have h := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (1 : ℝ) < 2) hc continuousOn_const
    (g := fun _ => (1 : ℝ))
    (fun t ht => Real.rpow_le_one_of_one_le_of_nonpos ht.1.le (by linarith))
    ⟨2, by constructor <;> norm_num, Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)⟩
  norm_num at h
  exact h

/-- A concrete positive parameter leaving half of the contraction gap. -/
def hardyAbsorptionParameter (s : ℝ) : ℝ := (1 - hardyAveragingConstant s) / (2 * hardyAveragingConstant s)

theorem hardyAbsorptionParameter_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) :
    0 < hardyAbsorptionParameter s := by
  exact div_pos (sub_pos.mpr (hardyAveragingConstant_lt_one hs hs₁))
    (mul_pos (by norm_num) (hardyAveragingConstant_pos hs))

theorem hardyAbsorptionParameter_identity {s : ℝ} (hs : 0 < s) :
    (1 + hardyAbsorptionParameter s) * hardyAveragingConstant s =
      (1 + hardyAveragingConstant s) / 2 := by
  unfold hardyAbsorptionParameter
  field_simp [(hardyAveragingConstant_pos hs).ne']
  ring

theorem hardyAbsorptionParameter_contracts {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) :
    (1 + hardyAbsorptionParameter s) * hardyAveragingConstant s < 1 := by
  rw [hardyAbsorptionParameter_identity hs]
  linarith [hardyAveragingConstant_lt_one hs hs₁]

/-- The adjustable square estimate used before averaging. -/
theorem norm_sq_le_weighted_difference {ε : ℝ} (hε : 0 < ε) (z w : ℂ) :
    ‖z‖ ^ 2 ≤ (1 + ε) * ‖w‖ ^ 2 + (1 + 1 / ε) * ‖z - w‖ ^ 2 := by
  have hn : ‖z‖ ≤ ‖w‖ + ‖z - w‖ := by
    have h := norm_add_le w (z - w)
    simpa only [add_sub_cancel, add_comm] using h
  have hh : (‖w‖ + ‖z - w‖) ^ 2 ≤ (1 + ε) * ‖w‖ ^ 2 + (1 + 1 / ε) * ‖z - w‖ ^ 2 := by
    apply (mul_le_mul_iff_right₀ hε).mp
    field_simp
    nlinarith [sq_nonneg (ε * ‖w‖ - ‖z - w‖)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)|>.mpr hn).trans hh

/-- On the averaging triangle the intrinsic difference kernel dominates its averaging weight. -/
theorem hardy_triangle_kernel_le {s x y : ℝ} (hs : 0 ≤ s) (hxy : x < y) (hy : y < 2 * x) :
    ENNReal.ofReal (x ^ (-(1 + 2 * s))) ≤ fractionalDistanceKernel s x y := by
  rw [fractionalDistanceKernel, abs_of_neg (sub_neg.mpr hxy), neg_sub]
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (sub_pos.mpr hxy) (by linarith) (by linarith)

/-- Exact real annular mass from reversing the averaging triangle. -/
theorem integral_hardy_annulus {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    (∫ x in (y / 2)..y, x ^ (-(1 + 2 * s))) =
      hardyAveragingConstant s * y ^ (-2 * s) := by
  have hz : (0 : ℝ) ∉ uIcc (y / 2) y := by
    rw [uIcc_of_le (by linarith)]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, hz⟩),
    show -(1 + 2 * s) + 1 = -2 * s by ring,
    Real.div_rpow hy.le (by norm_num), show -2 * s = -(2 * s) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  unfold hardyAveragingConstant
  field_simp
  ring

/-- Nonnegative annular mass, with finite integral justified away from zero. -/
theorem lintegral_hardy_annulus {s y : ℝ} (hs : 0 < s) (hy : 0 < y) :
    (∫⁻ x : ℝ in Ioo (y / 2) y, ENNReal.ofReal (x ^ (-(1 + 2 * s)))) =
      ENNReal.ofReal (hardyAveragingConstant s * y ^ (-2 * s)) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (-(1 + 2 * s))) (Ioo (y / 2) y) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + 2 * s) < -1)
    (show 0 < y / 2 by positivity)).mono_set Ioo_subset_Ioi_self
  have hn : 0 ≤ᵐ[volume.restrict (Ioo (y / 2) y)] fun x : ℝ => x ^ (-(1 + 2 * s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact Real.rpow_nonneg (by linarith [hx.1]) _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le (by linarith : y / 2 ≤ y), integral_hardy_annulus hs hy]

end NLS.Fourier
