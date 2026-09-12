import NLS.Fourier.FractionalHardy
import NLS.Fourier.IntrinsicIntervalEnergy

/-!
# A uniform intrinsic bound for exterior interaction

The positive Hardy gap is inverted explicitly. The resulting finite constant
controls exterior energy by the full intrinsic interval energy for arbitrary
square-integrable representatives, even when the fractional energy is infinite.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The coercive gap in the fractional Hardy estimate. -/
def fractionalHardyGap (s : ℝ) : ℝ≥0∞ :=
  1 - ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2)

theorem fractionalHardyGap_pos {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) : 0 < fractionalHardyGap s := by
  apply tsub_pos_iff_lt.mpr
  apply ENNReal.ofReal_lt_one.mpr
  linarith [hardyAveragingConstant_lt_one hs hs₁]

/-- An explicit uniform exterior bound constant; no optimality is claimed. -/
def fractionalExteriorBoundConstant (s L : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (1 / (2 * s)) * (fractionalHardyGap s)⁻¹ * 2 *
    (ENNReal.ofReal (1 + 1 / hardyAbsorptionParameter s) + ENNReal.ofReal ((L / 2) ^ (-2 * s)))

theorem fractionalExteriorBoundConstant_lt_top {s : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2) (L : ℝ) :
    fractionalExteriorBoundConstant s L < ⊤ := by
  unfold fractionalExteriorBoundConstant
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.inv_lt_top.mpr (fractionalHardyGap_pos hs hs₁))) (by norm_num))
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

private theorem fractionalExteriorEnergy_le_intrinsic_of_measurable {s L : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hL : 0 < L) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    fractionalExteriorEnergy s L f ≤ fractionalExteriorBoundConstant s L * intrinsicIntervalEnergy s L f := by
  have hg : fractionalHardyGap s ≠ 0 := (fractionalHardyGap_pos hs hs₁).ne'
  have hgt : fractionalHardyGap s ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) tsub_le_self
  have h := (ENNReal.mul_le_iff_le_inv hg hgt).mp (fractionalBoundaryWeight_hardy_bound hs hs₁ hL f hf hf₂)
  let b := ENNReal.ofReal (1 + 1 / hardyAbsorptionParameter s)
  let d := ENNReal.ofReal ((L / 2) ^ (-2 * s))
  have hi : b * fractionalIntervalEnergy s L f + d * intervalSquareEnergy L f ≤
      (b + d) * intrinsicIntervalEnergy s L f := by
    unfold intrinsicIntervalEnergy
    rw [mul_add]
    exact add_le_add
      (mul_le_mul' (le_add_right le_rfl) le_rfl)
      (mul_le_mul' (le_add_left le_rfl) le_rfl) |>.trans_eq (add_comm _ _)
  rw [fractionalExteriorEnergy_eq_boundary hs]
  calc
    _ ≤ ENNReal.ofReal (1 / (2 * s)) * ((fractionalHardyGap s)⁻¹ *
        (2 * (b * fractionalIntervalEnergy s L f + d * intervalSquareEnergy L f))) := mul_le_mul' le_rfl h
    _ ≤ ENNReal.ofReal (1 / (2 * s)) * ((fractionalHardyGap s)⁻¹ *
        (2 * ((b + d) * intrinsicIntervalEnergy s L f))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl hi))
    _ = _ := by simp only [fractionalExteriorBoundConstant, b, d, mul_assoc]

/-- Uniform exterior control from intrinsic data, with no global measurability assumption. -/
theorem fractionalExteriorEnergy_le_intrinsic {s L : ℝ}
    (hs : 0 < s) (hs₁ : s < 1 / 2) (hL : 0 < L) (f : ℝ → ℂ)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    fractionalExteriorEnergy s L f ≤ fractionalExteriorBoundConstant s L * intrinsicIntervalEnergy s L f := by
  let g := hf₂.aestronglyMeasurable.mk f
  have he : f =ᵐ[volume.restrict (Ioo 0 L)] g := hf₂.aestronglyMeasurable.ae_eq_mk
  have hg : Measurable g := hf₂.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  rw [fractionalExteriorEnergy_congr he, intrinsicIntervalEnergy_congr he]
  exact fractionalExteriorEnergy_le_intrinsic_of_measurable hs hs₁ hL g hg ((memLp_congr_ae he).mp hf₂)

end NLS.Fourier
