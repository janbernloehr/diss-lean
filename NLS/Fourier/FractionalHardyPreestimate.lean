import NLS.Fourier.FractionalHardyAveraging

/-!
# Truncated fractional Hardy preestimate

The averaged adjustable square inequality yields a uniform preestimate for the
actual endpoint-weighted square integral. No boundary integrability is assumed:
all expressions retain their extended nonnegative values. Absorption requires
proving the truncated boundary energy finite from `L²` first.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The left endpoint-weighted energy with a positive-distance cutoff. -/
def leftBoundaryEnergy (s δ L : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ x : ℝ in Ioo δ L, ENNReal.ofReal (x ^ (-2 * s)) * ENNReal.ofReal (‖f x‖ ^ 2)

/-- Exact row normalization recovers the truncated boundary energy of actual interval data. -/
theorem leftBoundaryEnergy_eq_averaging {s δ L : ℝ} (hδ : 0 ≤ δ) (f : ℝ → ℂ) :
    leftBoundaryEnergy s δ (L / 2) f =
      ∫⁻ x : ℝ in Ioo δ (L / 2), ∫⁻ y : ℝ in Ioo δ L,
        hardyAveragingKernel s x y * ENNReal.ofReal (‖f x‖ ^ 2) := by
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_hardyAveragingKernel_row_restrict hδ hx]

/-- The physical truncated Hardy preestimate, before justified absorption. -/
theorem leftBoundaryEnergy_preestimate {s δ L ε : ℝ} (hs : 0 < s) (hδ : 0 ≤ δ) (hε : 0 < ε)
    (f : ℝ → ℂ) (hf : Measurable f) :
    leftBoundaryEnergy s δ (L / 2) f ≤
      ENNReal.ofReal ((1 + ε) * hardyAveragingConstant s) * leftBoundaryEnergy s δ L f +
        ENNReal.ofReal (1 + 1 / ε) * fractionalIntervalEnergy s L f := by
  let μ := volume.restrict (Ioo δ (L / 2))
  let ν := volume.restrict (Ioo δ L)
  let F₀ := fun p : ℝ × ℝ => hardyAveragingKernel s p.1 p.2 * ENNReal.ofReal (‖f p.1‖ ^ 2)
  let F₁ := fun p : ℝ × ℝ => hardyAveragingKernel s p.1 p.2 * ENNReal.ofReal (‖f p.2‖ ^ 2)
  let F₂ := fun p : ℝ × ℝ => hardyAveragingKernel s p.1 p.2 * ENNReal.ofReal (‖f p.1 - f p.2‖ ^ 2)
  have hm₀ : Measurable F₀ := (measurable_hardyAveragingKernel s).mul (by fun_prop)
  have hm₁ : Measurable F₁ := (measurable_hardyAveragingKernel s).mul (by fun_prop)
  have hm₂ : Measurable F₂ := (measurable_hardyAveragingKernel s).mul (by fun_prop)
  have hA : 0 ≤ 1 + ε := by positivity
  have hB : 0 ≤ 1 + 1 / ε := by positivity
  have hpoint (p : ℝ × ℝ) : F₀ p ≤ ENNReal.ofReal (1 + ε) * F₁ p + ENNReal.ofReal (1 + 1 / ε) * F₂ p := by
    have h := mul_le_mul' (le_refl (hardyAveragingKernel s p.1 p.2))
      (ENNReal.ofReal_le_ofReal (norm_sq_le_weighted_difference hε (f p.1) (f p.2)))
    simpa only [F₀, F₁, F₂, ENNReal.ofReal_add (mul_nonneg hA (sq_nonneg _)) (mul_nonneg hB (sq_nonneg _)),
      ENNReal.ofReal_mul hA, ENNReal.ofReal_mul hB, mul_add, mul_left_comm] using h
  have h₁ : (∫⁻ p, F₁ p ∂μ.prod ν) ≤
      ENNReal.ofReal (hardyAveragingConstant s) * leftBoundaryEnergy s δ L f := by
    rw [lintegral_prod _ hm₁.aemeasurable]
    exact lintegral_hardyAveraging_restrict_le hs hδ _ (fun y => ENNReal.ofReal (‖f y‖ ^ 2)) (by fun_prop)
  have h₂ : (∫⁻ p, F₂ p ∂μ.prod ν) ≤ fractionalIntervalEnergy s L f := by
    rw [lintegral_prod _ hm₂.aemeasurable]
    exact hardyAveraging_difference_le hs.le hδ f
  calc
    leftBoundaryEnergy s δ (L / 2) f = ∫⁻ p, F₀ p ∂μ.prod ν := by
      rw [lintegral_prod _ hm₀.aemeasurable]
      exact leftBoundaryEnergy_eq_averaging hδ f
    _ ≤ ∫⁻ p, ENNReal.ofReal (1 + ε) * F₁ p + ENNReal.ofReal (1 + 1 / ε) * F₂ p ∂μ.prod ν :=
      lintegral_mono hpoint
    _ = ENNReal.ofReal (1 + ε) * (∫⁻ p, F₁ p ∂μ.prod ν) +
        ENNReal.ofReal (1 + 1 / ε) * (∫⁻ p, F₂ p ∂μ.prod ν) := by
      have hmA : Measurable (fun p => ENNReal.ofReal (1 + ε) * F₁ p) := measurable_const.mul hm₁
      rw [lintegral_add_left hmA,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ _ := by
      rw [ENNReal.ofReal_mul hA, mul_assoc]
      exact add_le_add (mul_le_mul' le_rfl h₁) (mul_le_mul' le_rfl h₂)

/-- Below half regularity the preestimate uses an explicit coefficient strictly below one. -/
theorem leftBoundaryEnergy_preestimate_contracting {s δ L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hδ : 0 ≤ δ) (f : ℝ → ℂ) (hf : Measurable f) :
    leftBoundaryEnergy s δ (L / 2) f ≤
      ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2) * leftBoundaryEnergy s δ L f +
        ENNReal.ofReal (1 + 1 / hardyAbsorptionParameter s) * fractionalIntervalEnergy s L f := by
  simpa only [hardyAbsorptionParameter_identity hs] using
    leftBoundaryEnergy_preestimate hs hδ (hardyAbsorptionParameter_pos hs hs₁) f hf

/-- A positive cutoff bounds the singular weight by a finite constant times the interval square energy. -/
theorem leftBoundaryEnergy_le_cutoff {s δ L : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ) (f : ℝ → ℂ) :
    leftBoundaryEnergy s δ L f ≤ ENNReal.ofReal (δ ^ (-2 * s)) *
      ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2) := by
  calc
    _ ≤ ∫⁻ x : ℝ in Ioo δ L, ENNReal.ofReal (δ ^ (-2 * s)) * ENNReal.ofReal (‖f x‖ ^ 2) := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro x hx
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal
        (Real.rpow_le_rpow_of_nonpos hδ hx.1.le (by linarith))) le_rfl
    _ = ENNReal.ofReal (δ ^ (-2 * s)) * ∫⁻ x : ℝ in Ioo δ L, ENNReal.ofReal (‖f x‖ ^ 2) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (lintegral_mono_set (Ioo_subset_Ioo hδ.le le_rfl))

/-- Truncated boundary energy is finite for arbitrary interval `L²` data before any absorption step. -/
theorem leftBoundaryEnergy_lt_top {s δ L : ℝ} (hs : 0 ≤ s) (hδ : 0 < δ)
    (f : ℝ → ℂ) (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    leftBoundaryEnergy s δ L f < ⊤ := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) (volume.restrict (Ioo 0 L)) :=
    hf.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hn : (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2)) < ⊤ :=
    (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => sq_nonneg _))).mp hi.2
  exact (leftBoundaryEnergy_le_cutoff hs hδ f).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hn)

end NLS.Fourier
