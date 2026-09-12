import NLS.Fourier.FractionalZeroExtension

/-!
# Physical translation form of the real-line fractional energy

A measure-preserving translation in the inner variable and Tonelli interchange
identify the real-line Gagliardo energy with the actual translation increment
energy. The identities retain infinite values.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- Actual fractional translation increment energy on the real line. -/
def fractionalLineTranslationEnergy (s : ℝ) (f : ℝ → ℂ) : ℝ≥0∞ :=
  ∫⁻ t : ℝ, ∫⁻ x : ℝ, ENNReal.ofReal (‖f (t + x) - f x‖ ^ 2) *
    ENNReal.ofReal (|t| ^ (-(1 + 2 * s)))

/-- The Gagliardo and translation double integrals agree for measurable real-line data. -/
theorem fractionalLineEnergy_eq_translation (s : ℝ) (f : ℝ → ℂ) (hf : Measurable f) :
    fractionalLineEnergy s f = fractionalLineTranslationEnergy s f := by
  let F := fun x t : ℝ => ENNReal.ofReal (‖f (t + x) - f x‖ ^ 2) *
    ENNReal.ofReal (|t| ^ (-(1 + 2 * s)))
  have hm : Measurable (Function.uncurry F) := by dsimp [F]; fun_prop
  calc
    _ = ∫⁻ x : ℝ, ∫⁻ t : ℝ, F x t := by
      apply lintegral_congr
      intro x
      have h := (measurePreserving_add_right volume x).lintegral_comp_emb
        (MeasurableEquiv.addRight x).measurableEmbedding
        (fun y => ENNReal.ofReal (‖f x - f y‖ ^ 2) * fractionalDistanceKernel s x y)
      have he (t : ℝ) : x - (t + x) = -t := by ring
      simpa only [F, fractionalDistanceKernel, he, abs_neg,
        norm_sub_rev (f x)] using h.symm
    _ = _ := lintegral_lintegral_swap hm.aemeasurable

/-- Translation energy respects almost-everywhere equality of real-line representatives. -/
theorem fractionalLineTranslationEnergy_congr {s : ℝ} {f g : ℝ → ℂ} (h : f =ᵐ[volume] g) :
    fractionalLineTranslationEnergy s f = fractionalLineTranslationEnergy s g := by
  apply lintegral_congr
  intro t
  apply lintegral_congr_ae
  have ht := (measurePreserving_add_left volume t).quasiMeasurePreserving.ae_eq h
  filter_upwards [h, ht] with x hx htx
  dsimp only [Function.comp_def] at htx
  rw [hx, htx]

/-- Translation and Gagliardo energy agree for arbitrary `L²` representatives. -/
theorem fractionalLineEnergy_eq_translation_of_memLp (s : ℝ) (f : ℝ → ℂ) (hf : MemLp f 2 volume) :
    fractionalLineEnergy s f = fractionalLineTranslationEnergy s f := by
  let g := hf.aestronglyMeasurable.mk f
  have he : f =ᵐ[volume] g := hf.aestronglyMeasurable.ae_eq_mk
  rw [fractionalLineEnergy_congr he, fractionalLineTranslationEnergy_congr he]
  exact fractionalLineEnergy_eq_translation s g hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable

/-- Exact translation-energy decomposition of arbitrary square-integrable interval zero extensions. -/
theorem fractionalLineTranslationEnergy_zeroExtension (s : ℝ) {L : ℝ} (f : ℝ → ℂ)
    (hf : MemLp f 2 (volume.restrict (Ioo 0 L))) :
    fractionalLineTranslationEnergy s (intervalZeroExtension L f) =
      fractionalIntervalEnergy s L f + 2 * fractionalExteriorEnergy s L f := by
  rw [← fractionalLineEnergy_eq_translation_of_memLp s _ ((memLp_intervalZeroExtension_iff L f).mpr hf),
    fractionalLineEnergy_zeroExtension s f hf]

/-- Below half, finite interval energy yields finite physical real-line translation energy. -/
theorem fractionalLineTranslationEnergy_zeroExtension_lt_top {s L : ℝ} (hs : 0 < s) (hs₁ : s < 1 / 2)
    (hL : 0 < L) (f : ℝ → ℂ) (hf : HasFractionalIntervalRegularity s L f) :
    fractionalLineTranslationEnergy s (intervalZeroExtension L f) < ⊤ := by
  rw [← fractionalLineEnergy_eq_translation_of_memLp s _ ((memLp_intervalZeroExtension_iff L f).mpr hf.1)]
  exact (fractionalLineEnergy_zeroExtension_lt_top_iff hs hs₁ hL f hf.1).mpr hf.2

end NLS.Fourier
