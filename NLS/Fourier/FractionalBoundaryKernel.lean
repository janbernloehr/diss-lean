import NLS.Fourier.FractionalSpectralBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Fractional interactions with the exterior of an interval

The exact exterior kernel mass produces the two endpoint Hardy weights.
All interaction energies use nonnegative integrals and may be infinite.
The interval length is arbitrary and positive.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The real-distance fractional kernel, assigned zero at the diagonal for `s>0`. -/
def fractionalDistanceKernel (s x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (|x - y| ^ (-(1 + 2 * s)))

/-- The weight contributed by both interval endpoints. -/
def fractionalBoundaryWeight (s L x : ℝ) : ℝ :=
  x ^ (-2 * s) + (L - x) ^ (-2 * s)

theorem fractionalBoundaryWeight_nonneg (s L : ℝ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    0 ≤ fractionalBoundaryWeight s L x := by
  exact add_nonneg (Real.rpow_nonneg hx.1 _) (Real.rpow_nonneg (sub_nonneg.mpr hx.2) _)

@[simp] theorem fractionalBoundaryWeight_reflect (s L x : ℝ) :
    fractionalBoundaryWeight s L (L - x) = fractionalBoundaryWeight s L x := by
  simp only [fractionalBoundaryWeight, sub_sub_cancel, add_comm]

/-- The nonnegative tail integral is an actual finite improper integral for positive distance. -/
theorem lintegral_fractional_tail {s d : ℝ} (hs : 0 < s) (hd : 0 < d) :
    (∫⁻ y : ℝ in Ioi d, ENNReal.ofReal (y ^ (-(1 + 2 * s)))) =
      ENNReal.ofReal (d ^ (-2 * s) / (2 * s)) := by
  have hi := integrableOn_Ioi_rpow_of_lt (by linarith : -(1 + 2 * s) < -1) hd
  have hn : 0 ≤ᵐ[volume.restrict (Ioi d)] fun y : ℝ => y ^ (-(1 + 2 * s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    exact Real.rpow_nonneg (hd.trans hy).le _
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    integral_Ioi_rpow_of_lt (by linarith : -(1 + 2 * s) < -1) hd]
  congr 1
  rw [show -(1 + 2 * s) + 1 = -2 * s by ring]
  ring

/-- The mass across the left endpoint is the left Hardy weight divided by `2s`. -/
theorem lintegral_fractionalDistanceKernel_left {s x : ℝ} (hs : 0 < s) (hx : 0 < x) :
    (∫⁻ y : ℝ in Iio 0, fractionalDistanceKernel s x y) =
      ENNReal.ofReal (x ^ (-2 * s) / (2 * s)) := by
  have hm : MeasurePreserving (fun y : ℝ => x - y) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume x).comp (Measure.measurePreserving_neg volume)
  have he : (fun y : ℝ => x - y) ⁻¹' Ioi x = Iio 0 := by
    ext y
    simp only [mem_preimage, mem_Ioi, mem_Iio]
    constructor <;> intro h <;> linarith
  have hh := hm.setLIntegral_comp_preimage (s := Ioi x) measurableSet_Ioi
    (f := fun y : ℝ => ENNReal.ofReal (y ^ (-(1 + 2 * s)))) (by fun_prop)
  rw [he] at hh
  calc
    _ = ∫⁻ y : ℝ in Iio 0, ENNReal.ofReal ((x - y) ^ (-(1 + 2 * s))) := by
      apply setLIntegral_congr_fun measurableSet_Iio
      intro y hy
      rw [fractionalDistanceKernel, abs_of_pos (by linarith [show y < 0 from hy])]
    _ = _ := hh.trans (lintegral_fractional_tail hs hx)

/-- The mass across the right endpoint is the right Hardy weight divided by `2s`. -/
theorem lintegral_fractionalDistanceKernel_right {s L x : ℝ} (hs : 0 < s) (hx : x < L) :
    (∫⁻ y : ℝ in Ioi L, fractionalDistanceKernel s x y) =
      ENNReal.ofReal ((L - x) ^ (-2 * s) / (2 * s)) := by
  have he : (fun y : ℝ => y - x) ⁻¹' Ioi (L - x) = Ioi L := by
    ext y
    simp only [mem_preimage, mem_Ioi, sub_lt_sub_iff_right]
  have hh := (measurePreserving_sub_right volume x).setLIntegral_comp_preimage (s := Ioi (L - x)) measurableSet_Ioi
    (f := fun y : ℝ => ENNReal.ofReal (y ^ (-(1 + 2 * s)))) (by fun_prop)
  rw [he] at hh
  calc
    _ = ∫⁻ y : ℝ in Ioi L, ENNReal.ofReal ((y - x) ^ (-(1 + 2 * s))) := by
      apply setLIntegral_congr_fun measurableSet_Ioi
      intro y hy
      rw [fractionalDistanceKernel, abs_of_neg (by linarith [show L < y from hy]), neg_sub]
    _ = _ := hh.trans (lintegral_fractional_tail hs (sub_pos.mpr hx))

/-- The full exterior mass, with no endpoint matching assumption on interval data. -/
theorem lintegral_fractionalDistanceKernel_exterior {s L x : ℝ} (hs : 0 < s) (hx : x ∈ Ioo 0 L) :
    (∫⁻ y : ℝ in (Icc 0 L)ᶜ, fractionalDistanceKernel s x y) =
      ENNReal.ofReal (fractionalBoundaryWeight s L x / (2 * s)) := by
  have he : (Icc 0 L)ᶜ = Iio 0 ∪ Ioi L := by
    ext y
    simp only [mem_compl_iff, mem_Icc, not_and_or, not_le, mem_union, mem_Iio, mem_Ioi]
  rw [he, lintegral_union measurableSet_Ioi (by
    apply disjoint_left.mpr
    intro y hy hz
    have : 0 < L := hx.1.trans hx.2
    linarith [show y < 0 from hy, show L < y from hz]),
    lintegral_fractionalDistanceKernel_left hs hx.1,
    lintegral_fractionalDistanceKernel_right hs hx.2]
  rw [fractionalBoundaryWeight, add_div, ENNReal.ofReal_add
    (div_nonneg (Real.rpow_nonneg hx.1.le _) (by positivity))
    (div_nonneg (Real.rpow_nonneg (sub_pos.mpr hx.2).le _) (by positivity))]

/-- Interaction of interval data with its zero values on the exterior. -/
def fractionalExteriorEnergy (s L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ in Ioo 0 L, ∫⁻ y : ℝ in (Icc 0 L)ᶜ,
    ENNReal.ofReal (‖f x‖ ^ 2) * fractionalDistanceKernel s x y

/-- Exact Hardy-weight formula, valid even when the exterior energy is infinite. -/
theorem fractionalExteriorEnergy_eq_boundary {s : ℝ} (hs : 0 < s) (L : ℝ) (f : ℝ → ℂ) :
    fractionalExteriorEnergy s L f =
      ENNReal.ofReal (1 / (2 * s)) *
        ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (fractionalBoundaryWeight s L x * ‖f x‖ ^ 2) := by
  rw [fractionalExteriorEnergy, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_fractionalDistanceKernel_exterior hs hx,
    ENNReal.ofReal_mul (fractionalBoundaryWeight_nonneg s L ⟨hx.1.le, hx.2.le⟩)]
  rw [div_eq_mul_inv, ENNReal.ofReal_mul (fractionalBoundaryWeight_nonneg s L ⟨hx.1.le, hx.2.le⟩),
    one_div]
  ring

/-- The intrinsic interval Gagliardo energy, with no interaction across endpoints. -/
def fractionalIntervalEnergy (s L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ in Ioo 0 L, ∫⁻ y : ℝ in Ioo 0 L,
    ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalDistanceKernel s x y

@[simp] theorem fractionalIntervalEnergy_const (s L : ℝ) (z : ℂ) :
    fractionalIntervalEnergy s L (fun _ => z) = 0 := by
  simp [fractionalIntervalEnergy]

/-- Intrinsic interval energy depends only on the almost-everywhere interval data. -/
theorem fractionalIntervalEnergy_congr {s L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) :
    fractionalIntervalEnergy s L f = fractionalIntervalEnergy s L g := by
  apply lintegral_congr_ae
  filter_upwards [h] with x hx
  apply lintegral_congr_ae
  filter_upwards [h] with y hy
  rw [hx, hy]

/-- The exterior energy is precisely the mixed part of the zero-extension difference energy. -/
theorem fractionalExteriorEnergy_eq_zeroExtension (s L : ℝ) (f : ℝ → ℂ) :
    fractionalExteriorEnergy s L f =
      ∫⁻ x : ℝ in Ioo 0 L, ∫⁻ y : ℝ in (Icc 0 L)ᶜ,
        ENNReal.ofReal (‖(Ioo 0 L).indicator f x - (Ioo 0 L).indicator f y‖ ^ 2) *
          fractionalDistanceKernel s x y := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  apply setLIntegral_congr_fun measurableSet_Icc.compl
  intro y hy
  have hy' : y ∉ Ioo 0 L := fun h => hy ⟨h.1.le, h.2.le⟩
  simp only [indicator_of_mem hx, indicator_of_notMem hy', sub_zero]

/-- Exterior energy is monotone under almost-everywhere control of the interval magnitudes. -/
theorem fractionalExteriorEnergy_mono {s L : ℝ} {f g : ℝ → ℂ}
    (h : ∀ᵐ x ∂volume.restrict (Ioo 0 L), ‖f x‖ ≤ ‖g x‖) :
    fractionalExteriorEnergy s L f ≤ fractionalExteriorEnergy s L g := by
  apply lintegral_mono_ae
  filter_upwards [h] with x hx
  apply lintegral_mono
  intro y
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)|>.mpr hx)) le_rfl

end NLS.Fourier
