import NLS.Fourier.FractionalBoundaryKernel

/-!
# The sharp endpoint-weight threshold

The exterior interaction weight is integrable exactly below half regularity.
Its mass and the exterior energy of constant interval data are computed without
using a totalized integral to assert finiteness at or above the threshold.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

theorem measurable_fractionalBoundaryWeight (s L : ℝ) : Measurable (fractionalBoundaryWeight s L) := by
  unfold fractionalBoundaryWeight
  fun_prop

/-- Below one half, the two endpoint weights are integrable on any finite interval. -/
theorem intervalIntegrable_fractionalBoundaryWeight {s L : ℝ} (hs : s < 1 / 2) :
    IntervalIntegrable (fractionalBoundaryWeight s L) volume 0 L := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (-2 * s)) volume 0 L :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hj : IntervalIntegrable (fun x : ℝ => (L - x) ^ (-2 * s)) volume 0 L := by
    simpa using (hi.comp_sub_left L).symm
  exact hi.add hj

/-- Necessity includes divergence at exactly one half. -/
theorem integrableOn_fractionalBoundaryWeight_iff {s L : ℝ} (hL : 0 < L) :
    IntegrableOn (fractionalBoundaryWeight s L) (Ioo 0 L) ↔ s < 1 / 2 := by
  constructor
  · intro h
    have hi : IntegrableOn (fun x : ℝ => x ^ (-2 * s)) (Ioo 0 L) := by
      apply h.mono' (by fun_prop)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hx.1.le _)]
      exact le_add_of_nonneg_right (Real.rpow_nonneg (sub_pos.mpr hx.2).le _)
    have hp := (intervalIntegral.integrableOn_Ioo_rpow_iff hL).mp hi
    linarith
  · intro hs
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le).mp
      (intervalIntegrable_fractionalBoundaryWeight hs)

/-- The exact integral of the Hardy weight below its threshold. -/
theorem integral_fractionalBoundaryWeight {s L : ℝ} (hs : s < 1 / 2) :
    (∫ x in (0 : ℝ)..L, fractionalBoundaryWeight s L x) =
      2 * L ^ (1 - 2 * s) / (1 - 2 * s) := by
  have hi : IntervalIntegrable (fun x : ℝ => x ^ (-2 * s)) volume 0 L :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  have hj : IntervalIntegrable (fun x : ℝ => (L - x) ^ (-2 * s)) volume 0 L := by
    simpa using (hi.comp_sub_left L).symm
  simp only [fractionalBoundaryWeight]
  rw [intervalIntegral.integral_add hi hj,
    intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-2 * s)) L]
  simp only [sub_self, sub_zero]
  rw [integral_rpow (Or.inl (by linarith : -1 < -2 * s))]
  rw [show -2 * s + 1 = 1 - 2 * s by ring, Real.zero_rpow (by linarith : 1 - 2 * s ≠ 0)]
  ring

/-- Extended nonnegative mass of the boundary weight, with integrability proved first. -/
theorem lintegral_fractionalBoundaryWeight {s L : ℝ} (hs : s < 1 / 2) (hL : 0 < L) :
    (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (fractionalBoundaryWeight s L x)) =
      ENNReal.ofReal (2 * L ^ (1 - 2 * s) / (1 - 2 * s)) := by
  have hi := (integrableOn_fractionalBoundaryWeight_iff hL).mpr hs
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 L)] fractionalBoundaryWeight s L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact fractionalBoundaryWeight_nonneg s L ⟨hx.1.le, hx.2.le⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn, ← integral_Ioc_eq_integral_Ioo,
    ← intervalIntegral.integral_of_le hL.le, integral_fractionalBoundaryWeight hs]

/-- The nonnegative boundary mass is finite exactly below one half. -/
theorem lintegral_fractionalBoundaryWeight_lt_top_iff {s L : ℝ} (hL : 0 < L) :
    (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (fractionalBoundaryWeight s L x)) < ⊤ ↔ s < 1 / 2 := by
  have hn : 0 ≤ᵐ[volume.restrict (Ioo 0 L)] fractionalBoundaryWeight s L := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact fractionalBoundaryWeight_nonneg s L ⟨hx.1.le, hx.2.le⟩
  rw [← hasFiniteIntegral_iff_ofReal hn, ← integrableOn_fractionalBoundaryWeight_iff hL]
  exact ⟨fun h => ⟨(measurable_fractionalBoundaryWeight s L).aestronglyMeasurable, h⟩, fun h => h.2⟩

/-- Constant interval data has finite exterior interaction precisely below one half. -/
theorem fractionalExteriorEnergy_one_lt_top_iff {s L : ℝ} (hs : 0 < s) (hL : 0 < L) :
    fractionalExteriorEnergy s L (fun _ => 1) < ⊤ ↔ s < 1 / 2 := by
  rw [fractionalExteriorEnergy_eq_boundary hs]
  simp only [norm_one, one_pow, mul_one]
  have hc : ENNReal.ofReal (1 / (2 * s)) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (by positivity)
  rw [ENNReal.mul_lt_top_iff]
  constructor
  · rintro (h | h | h)
    · exact (lintegral_fractionalBoundaryWeight_lt_top_iff hL).mp h.2
    · exact (hc h).elim
    · exact (lintegral_fractionalBoundaryWeight_lt_top_iff hL).mp (h ▸ ENNReal.zero_lt_top)
  · intro h
    exact Or.inl ⟨ENNReal.ofReal_lt_top, (lintegral_fractionalBoundaryWeight_lt_top_iff hL).mpr h⟩

/-- Exact exterior energy of a constant amplitude below one half. -/
theorem fractionalExteriorEnergy_const {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (z : ℂ) :
    fractionalExteriorEnergy s L (fun _ => z) =
      ENNReal.ofReal (L ^ (1 - 2 * s) * ‖z‖ ^ 2 / (s * (1 - 2 * s))) := by
  rw [fractionalExteriorEnergy_eq_boundary hs]
  have he : (fun x : ℝ => ENNReal.ofReal (fractionalBoundaryWeight s L x * ‖z‖ ^ 2)) =
      fun x => ENNReal.ofReal (‖z‖ ^ 2) * ENNReal.ofReal (fractionalBoundaryWeight s L x) := by
    funext x
    rw [mul_comm, ENNReal.ofReal_mul (sq_nonneg _)]
  rw [he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_fractionalBoundaryWeight hs₁ hL,
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / (2 * s))]
  congr 1
  field_simp

/-- An almost-everywhere bounded interval function has controlled exterior interaction below half. -/
theorem fractionalExteriorEnergy_le_of_bounded {s L M : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (hM : 0 ≤ M) (f : ℝ → ℂ)
    (hf : ∀ᵐ x ∂volume.restrict (Ioo 0 L), ‖f x‖ ≤ M) :
    fractionalExteriorEnergy s L f ≤
      ENNReal.ofReal (L ^ (1 - 2 * s) * M ^ 2 / (s * (1 - 2 * s))) := by
  have h := fractionalExteriorEnergy_mono (s := s) (g := fun _ => (M : ℂ)) (by
    simpa only [Complex.norm_real, Real.norm_of_nonneg hM] using hf)
  simpa only [fractionalExteriorEnergy_const hs hs₁ hL, Complex.norm_real,
    Real.norm_of_nonneg hM] using h

end NLS.Fourier
