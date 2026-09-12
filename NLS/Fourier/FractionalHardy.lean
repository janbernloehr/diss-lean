import NLS.Fourier.FractionalHardyLeft

/-!
# Fractional Hardy control of both interval endpoints

Reflection transfers the left endpoint estimate to the right. Consequently,
finite intrinsic interval fractional energy and `L²` control the actual
zero-extension exterior interaction throughout `0<s<1/2`.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Reflection preserves restricted interval Lebesgue measure. -/
theorem measurePreserving_interval_reflection (L : ℝ) :
    MeasurePreserving (fun x : ℝ => L - x) (volume.restrict (Ioo 0 L)) (volume.restrict (Ioo 0 L)) := by
  have hm : MeasurePreserving (fun x : ℝ => L - x) volume volume := by
    simpa only [Function.comp_def, sub_eq_add_neg] using
      (measurePreserving_add_left volume L).comp (Measure.measurePreserving_neg volume)
  have he : (fun x : ℝ => L - x) ⁻¹' Ioo 0 L = Ioo 0 L := by
    ext x
    simp only [mem_preimage, mem_Ioo]
    constructor <;> intro h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩
  simpa only [he] using hm.restrict_preimage (s := Ioo 0 L) measurableSet_Ioo

theorem measurableEmbedding_interval_reflection (L : ℝ) :
    MeasurableEmbedding (fun x : ℝ => L - x) := by
  simpa only [sub_eq_add_neg] using!
    ((MeasurableEquiv.neg ℝ).trans (MeasurableEquiv.addLeft L)).measurableEmbedding

@[simp] theorem fractionalDistanceKernel_reflect (s L x y : ℝ) :
    fractionalDistanceKernel s (L - x) (L - y) = fractionalDistanceKernel s x y := by
  simp only [fractionalDistanceKernel, sub_sub_sub_cancel_left, abs_sub_comm]

/-- Reflection preserves the intrinsic interval energy, including infinite energies. -/
theorem fractionalIntervalEnergy_reflect (s L : ℝ) (f : ℝ → ℂ) :
    fractionalIntervalEnergy s L (fun x => f (L - x)) = fractionalIntervalEnergy s L f := by
  let μ := volume.restrict (Ioo 0 L)
  let G := fun x y : ℝ => ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalDistanceKernel s x y
  have hm := measurePreserving_interval_reflection L
  have he := measurableEmbedding_interval_reflection L
  calc
    _ = ∫⁻ x, ∫⁻ y, G (L - x) (L - y) ∂μ ∂μ := by
      simp only [G, fractionalIntervalEnergy, μ, fractionalDistanceKernel_reflect]
    _ = ∫⁻ x, ∫⁻ y, G (L - x) y ∂μ ∂μ := by
      apply lintegral_congr
      intro x
      exact hm.lintegral_comp_emb he (G (L - x))
    _ = _ := hm.lintegral_comp_emb he (fun x => ∫⁻ y, G x y ∂μ)

/-- Reflection preserves the unweighted interval square energy. -/
theorem intervalSquareEnergy_reflect (L : ℝ) (f : ℝ → ℂ) :
    (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f (L - x)‖ ^ 2)) =
      ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2) :=
  (measurePreserving_interval_reflection L).lintegral_comp_emb
    (measurableEmbedding_interval_reflection L) (fun x => ENNReal.ofReal (‖f x‖ ^ 2))

/-- The two boundary contributions are the left energies of the function and its reflection. -/
theorem boundaryWeightEnergy_eq_left_add_reflect (s L : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (fractionalBoundaryWeight s L x * ‖f x‖ ^ 2)) =
      leftBoundaryEnergy s 0 L f + leftBoundaryEnergy s 0 L (fun x => f (L - x)) := by
  have he : leftBoundaryEnergy s 0 L (fun x => f (L - x)) =
      ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal ((L - x) ^ (-2 * s)) * ENNReal.ofReal (‖f x‖ ^ 2) := by
    have h := (measurePreserving_interval_reflection L).lintegral_comp_emb
      (measurableEmbedding_interval_reflection L)
      (fun x => ENNReal.ofReal ((L - x) ^ (-2 * s)) * ENNReal.ofReal (‖f x‖ ^ 2))
    simpa only [sub_sub_cancel] using! h
  rw [he, leftBoundaryEnergy, ← lintegral_add_left (show Measurable
    (fun x : ℝ => ENNReal.ofReal (x ^ (-2 * s)) * ENNReal.ofReal (‖f x‖ ^ 2)) by fun_prop)]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [fractionalBoundaryWeight, add_mul, ENNReal.ofReal_add
    (mul_nonneg (Real.rpow_nonneg hx.1.le _) (sq_nonneg _))
    (mul_nonneg (Real.rpow_nonneg (sub_pos.mpr hx.2).le _) (sq_nonneg _)),
    ENNReal.ofReal_mul (Real.rpow_nonneg hx.1.le _),
    ENNReal.ofReal_mul (Real.rpow_nonneg (sub_pos.mpr hx.2).le _)]

/-- Quantitative Hardy control of both boundary weights for measurable interval `L²` data. -/
theorem fractionalBoundaryWeight_hardy_bound {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    (1 - ENNReal.ofReal ((1 + hardyAveragingConstant s) / 2)) *
        (∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (fractionalBoundaryWeight s L x * ‖f x‖ ^ 2)) ≤
      2 * (ENNReal.ofReal (1 + 1 / hardyAbsorptionParameter s) * fractionalIntervalEnergy s L f +
        ENNReal.ofReal ((L / 2) ^ (-2 * s)) * ∫⁻ x : ℝ in Ioo 0 L, ENNReal.ofReal (‖f x‖ ^ 2)) := by
  have hr := leftBoundaryEnergy_hardy_bound hs hs₁ hL (fun x => f (L - x)) (by fun_prop)
    (hf₂.comp_measurePreserving (measurePreserving_interval_reflection L))
  rw [fractionalIntervalEnergy_reflect, intervalSquareEnergy_reflect] at hr
  rw [boundaryWeightEnergy_eq_left_add_reflect s L f hf, mul_add, two_mul]
  exact add_le_add (leftBoundaryEnergy_hardy_bound hs hs₁ hL f hf hf₂) hr

/-- General interval data with finite intrinsic energy has finite zero-extension interaction. -/
theorem fractionalExteriorEnergy_lt_top_of_measurable {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf : Measurable f)
    (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L))) (hE : fractionalIntervalEnergy s L f < ⊤) :
    fractionalExteriorEnergy s L f < ⊤ := by
  have hl := leftBoundaryEnergy_lt_top_of_interval hs hs₁ hL f hf hf₂ hE
  have hr := leftBoundaryEnergy_lt_top_of_interval hs hs₁ hL (fun x => f (L - x)) (by fun_prop)
    (hf₂.comp_measurePreserving (measurePreserving_interval_reflection L))
    (by simpa only [fractionalIntervalEnergy_reflect] using hE)
  rw [fractionalExteriorEnergy_eq_boundary hs, boundaryWeightEnergy_eq_left_add_reflect s L f hf]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨hl, hr⟩)

/-- Exterior interaction depends only on the almost-everywhere interval values. -/
theorem fractionalExteriorEnergy_congr {s L : ℝ} {f g : ℝ → ℂ}
    (h : f =ᵐ[volume.restrict (Ioo 0 L)] g) : fractionalExteriorEnergy s L f = fractionalExteriorEnergy s L g := by
  apply le_antisymm
  · exact fractionalExteriorEnergy_mono (h.mono (fun _ hx => le_of_eq (congrArg norm hx)))
  · exact fractionalExteriorEnergy_mono (h.mono (fun _ hx => le_of_eq (congrArg norm hx.symm)))

/-- Fractional Hardy finiteness for arbitrary `L²` interval representatives, with no global measurability assumption. -/
theorem fractionalExteriorEnergy_lt_top_of_interval {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf₂ : MemLp f 2 (volume.restrict (Ioo 0 L)))
    (hE : fractionalIntervalEnergy s L f < ⊤) : fractionalExteriorEnergy s L f < ⊤ := by
  let g := hf₂.aestronglyMeasurable.mk f
  have he : f =ᵐ[volume.restrict (Ioo 0 L)] g := hf₂.aestronglyMeasurable.ae_eq_mk
  have hg : Measurable g := hf₂.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  rw [fractionalExteriorEnergy_congr he]
  exact fractionalExteriorEnergy_lt_top_of_measurable hs hs₁ hL g hg ((memLp_congr_ae he).mp hf₂)
    (by simpa only [fractionalIntervalEnergy_congr he] using hE)

end NLS.Fourier
