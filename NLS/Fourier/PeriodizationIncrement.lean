import NLS.Fourier.FractionalLineTranslation

/-!
# Periodic increments from three zero-extension translates

For displacements at most one on a period-two interval, at most three adjacent
zero-extension translates enter the periodic increment. The resulting `L²`
increment bound holds without assuming the line increment energy finite.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The actual periodic increment as a sum of three zero-extension increments, away from endpoints. -/
theorem periodic_increment_eq_zeroExtension_sum (f : ℝ → ℂ) (hf : Function.Periodic f 2)
    {t x : ℝ} (ht : t ∈ Icc (-1) 1) (hx : x ∈ Ioo 0 2) (h₀ : t + x ≠ 0) (h₂ : t + x ≠ 2) :
    f (t + x) - f x =
      (intervalZeroExtension 2 f (t + x) - intervalZeroExtension 2 f x) +
      (intervalZeroExtension 2 f (t + (x + 2)) - intervalZeroExtension 2 f (x + 2)) +
      (intervalZeroExtension 2 f (t + (x - 2)) - intervalZeroExtension 2 f (x - 2)) := by
  have hxplus : x + 2 ∉ Ioo (0 : ℝ) 2 := by intro h; linarith [h.2, hx.1]
  have hxminus : x - 2 ∉ Ioo (0 : ℝ) 2 := by intro h; linarith [h.1, hx.2]
  rw [intervalZeroExtension_of_mem f hx, intervalZeroExtension_of_notMem f hxplus,
    intervalZeroExtension_of_notMem f hxminus, sub_zero, sub_zero]
  have hp : f (t + (x + 2)) = f (t + x) := by simpa only [add_assoc] using hf (t + x)
  have hm : f (t + (x - 2)) = f (t + x) := by
    have h := hf (t + (x - 2))
    convert h.symm using 1
    congr 1
    ring
  rcases lt_or_gt_of_ne h₀ with hy | hy
  · rw [intervalZeroExtension_of_notMem f (show t + x ∉ Ioo (0 : ℝ) 2 from fun h => hy.not_gt h.1),
      intervalZeroExtension_of_mem f (show t + (x + 2) ∈ Ioo (0 : ℝ) 2 from ⟨by linarith [ht.1, hx.1], by linarith⟩),
      intervalZeroExtension_of_notMem f (show t + (x - 2) ∉ Ioo (0 : ℝ) 2 from by intro h; linarith [h.1]), hp]
    ring
  · rcases lt_or_gt_of_ne h₂ with hy₂ | hy₂
    · rw [intervalZeroExtension_of_mem f ⟨hy, hy₂⟩,
        intervalZeroExtension_of_notMem f (show t + (x + 2) ∉ Ioo (0 : ℝ) 2 from by intro h; linarith [h.2]),
        intervalZeroExtension_of_notMem f (show t + (x - 2) ∉ Ioo (0 : ℝ) 2 from by intro h; linarith [h.1])]
      ring
    · rw [intervalZeroExtension_of_notMem f (show t + x ∉ Ioo (0 : ℝ) 2 from fun h => hy₂.not_gt h.2),
        intervalZeroExtension_of_notMem f (show t + (x + 2) ∉ Ioo (0 : ℝ) 2 from by intro h; linarith [h.2]),
        intervalZeroExtension_of_mem f (show t + (x - 2) ∈ Ioo (0 : ℝ) 2 from ⟨by linarith, by linarith [ht.2, hx.2]⟩), hm]
      ring

/-- A quantitative three-term square estimate. -/
theorem norm_add_three_sq_le (a b c : ℂ) :
    ‖a + b + c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) := by
  have h : ‖a + b + c‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ :=
    (norm_add_le _ _).trans (add_le_add_left (norm_add_le _ _) _)
  have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr h
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), sq_nonneg (‖b‖ - ‖c‖), sq_nonneg (‖a‖ - ‖c‖)]

/-- Three translated interval integrals are bounded by three full-line integrals. -/
theorem lintegral_three_translates_le (h : ℝ → ℝ≥0∞) (hh : Measurable h) :
    (∫⁻ x : ℝ in Ioo 0 2, h x + h (x + 2) + h (x - 2)) ≤ 3 * ∫⁻ x : ℝ, h x := by
  have hp : Measurable (fun x : ℝ => h (x + 2)) := hh.comp (by fun_prop)
  have hm : Measurable (fun x : ℝ => h (x - 2)) := hh.comp (by fun_prop)
  have hpi : (∫⁻ x : ℝ in Ioo 0 2, h (x + 2)) ≤ ∫⁻ x : ℝ, h x := by
    refine (setLIntegral_le_lintegral _ _).trans_eq ?_
    exact (measurePreserving_add_right volume (2 : ℝ)).lintegral_comp hh
  have hmi : (∫⁻ x : ℝ in Ioo 0 2, h (x - 2)) ≤ ∫⁻ x : ℝ, h x := by
    refine (setLIntegral_le_lintegral _ _).trans_eq ?_
    exact (measurePreserving_sub_right volume (2 : ℝ)).lintegral_comp hh
  have hsum : Measurable (fun x => h x + h (x + 2)) := hh.add hp
  rw [lintegral_add_left hsum, lintegral_add_left hh]
  calc
    _ ≤ (∫⁻ x : ℝ, h x) + (∫⁻ x : ℝ, h x) + (∫⁻ x : ℝ, h x) :=
      add_le_add (add_le_add (setLIntegral_le_lintegral _ _) hpi) hmi
    _ = _ := by ring

/-- Periodic square increments are controlled by line increments of the actual zero extension. -/
theorem periodic_increment_square_le_line (f : ℝ → ℂ) (hf : Function.Periodic f 2) (hm : Measurable f)
    {t : ℝ} (ht : t ∈ Icc (-1) 1) :
    (∫⁻ x : ℝ in Ioo 0 2, ENNReal.ofReal (‖f (t + x) - f x‖ ^ 2)) ≤
      9 * ∫⁻ x : ℝ, ENNReal.ofReal (‖intervalZeroExtension 2 f (t + x) - intervalZeroExtension 2 f x‖ ^ 2) := by
  let g := intervalZeroExtension 2 f
  let h := fun x : ℝ => ENNReal.ofReal (‖g (t + x) - g x‖ ^ 2)
  have hg : Measurable g := hm.indicator measurableSet_Ioo
  have hh : Measurable h := by dsimp [h]; fun_prop
  have hne₀ : ∀ᵐ x : ℝ ∂volume, x ≠ -t := by simp [ae_iff]
  have hne₂ : ∀ᵐ x : ℝ ∂volume, x ≠ 2 - t := by simp [ae_iff]
  calc
    _ ≤ ∫⁻ x : ℝ in Ioo 0 2, 3 * (h x + h (x + 2) + h (x - 2)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo,
        ae_restrict_of_ae hne₀, ae_restrict_of_ae hne₂] with x hx h₀ h₂
      have hn := norm_add_three_sq_le (g (t + x) - g x)
        (g (t + (x + 2)) - g (x + 2)) (g (t + (x - 2)) - g (x - 2))
      rw [← periodic_increment_eq_zeroExtension_sum f hf ht hx (by intro he; apply h₀; linarith)
        (by intro he; apply h₂; linarith)] at hn
      have he := ENNReal.ofReal_le_ofReal hn
      simpa only [h, g, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
        ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
        ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)] using he
    _ = 3 * ∫⁻ x : ℝ in Ioo 0 2, h x + h (x + 2) + h (x - 2) :=
      lintegral_const_mul' _ _ (by norm_num)
    _ ≤ 3 * (3 * ∫⁻ x : ℝ, h x) := mul_le_mul' le_rfl (lintegral_three_translates_le h hh)
    _ = _ := by dsimp [h, g]; ring

end NLS.Fourier
