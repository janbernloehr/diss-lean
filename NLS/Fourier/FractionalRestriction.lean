import NLS.Fourier.IntervalSobolevBound

/-!
# Restriction of periodic fractional regularity to an interval

The interval difference energy is bounded by full-line displacement energy
of the periodic representative. The kernel tail has finite mass `1/s` for
`s>0`; the uniform `L²` increment bound controls that tail.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace NLS.Fourier

/-- The real-distance version of the displacement kernel, with finite value zero at a negative-power singularity. -/
def realFractionalKernel (s t : ℝ) : ℝ≥0∞ := ENNReal.ofReal (|t| ^ (-(1 + 2 * s)))

@[fun_prop] theorem measurable_realFractionalKernel (s : ℝ) : Measurable (realFractionalKernel s) := by
  unfold realFractionalKernel
  fun_prop

/-- Restricting the inner spatial integral bounds interval energy by full displacement energy. -/
theorem fractionalIntervalEnergy_le_full_translation (s : ℝ) (f : CircleL2) :
    fractionalIntervalEnergy s 2 (circlePullback f) ≤
      2 * translationEnergy volume (realFractionalKernel s) f := by
  let G := fun x t : ℝ => ENNReal.ofReal (‖circlePullback f (t + x) - circlePullback f x‖ ^ 2) * realFractionalKernel s t
  have hm : Measurable (Function.uncurry G) := by
    dsimp only [G, realFractionalKernel, Function.uncurry_def]
    have hf := measurable_circlePullback f
    fun_prop
  have hd := translationEnergy_eq_double_lintegral volume (realFractionalKernel s) f
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm] at hd
  calc
    _ ≤ ∫⁻ x : ℝ in Ioo 0 2, ∫⁻ y : ℝ,
        ENNReal.ofReal (‖circlePullback f x - circlePullback f y‖ ^ 2) * fractionalDistanceKernel s x y := by
      apply lintegral_mono
      intro x
      exact setLIntegral_le_lintegral _ _
    _ = ∫⁻ x : ℝ in Ioo 0 2, ∫⁻ t : ℝ, G x t := by
      apply lintegral_congr
      intro x
      have h := (measurePreserving_add_right volume x).lintegral_comp_emb
        (MeasurableEquiv.addRight x).measurableEmbedding
        (fun y => ENNReal.ofReal (‖circlePullback f x - circlePullback f y‖ ^ 2) * fractionalDistanceKernel s x y)
      have he (t : ℝ) : x - (t + x) = -t := by ring
      simpa only [G, realFractionalKernel, fractionalDistanceKernel, he, abs_neg,
        norm_sub_rev (circlePullback f x)] using h.symm
    _ = ∫⁻ t : ℝ, ∫⁻ x : ℝ in Ioo 0 2, G x t := lintegral_lintegral_swap hm.aemeasurable
    _ = _ := by
      rw [hd, ← mul_assoc]
      have htwo : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 2 : ℝ) = 1 := by
        rw [← ENNReal.ofReal_ofNat, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      rw [htwo, one_mul]
      apply lintegral_congr
      intro t
      apply lintegral_congr
      intro x
      exact mul_comm _ _

/-- The large-displacement kernel has total mass `1/s`. -/
theorem lintegral_realFractionalKernel_tail {s : ℝ} (hs : 0 < s) :
    (∫⁻ t : ℝ in (Icc (-1) 1)ᶜ, realFractionalKernel s t) = ENNReal.ofReal (1 / s) := by
  have he : (fun t : ℝ => t + 1) ⁻¹' (Icc 0 2)ᶜ = (Icc (-1) 1)ᶜ := by
    ext t
    simp only [mem_preimage, mem_compl_iff, mem_Icc]
    constructor <;> contrapose! <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
  have h := (measurePreserving_add_right volume (1 : ℝ)).setLIntegral_comp_preimage
    (s := (Icc 0 2)ᶜ) measurableSet_Icc.compl (f := fractionalDistanceKernel s 1) (by
      unfold fractionalDistanceKernel
      fun_prop)
  rw [he] at h
  have hk : (fun t : ℝ => fractionalDistanceKernel s 1 (t + 1)) = realFractionalKernel s := by
    funext t
    simp only [fractionalDistanceKernel, realFractionalKernel, show 1 - (t + 1) = -t by ring, abs_neg]
  rw [hk, lintegral_fractionalDistanceKernel_exterior hs (by norm_num : (1 : ℝ) ∈ Ioo 0 2)] at h
  convert h using 1
  simp only [fractionalBoundaryWeight, show (2 : ℝ) - 1 = 1 by norm_num, Real.one_rpow]
  congr 1
  field_simp
  norm_num

/-- The real-kernel central displacement integral is exactly the periodic fractional energy. -/
theorem translationEnergy_realFractionalKernel_central (s : ℝ) (f : CircleL2) :
    translationEnergy (volume.restrict (Icc (-1) 1)) (realFractionalKernel s) f = fractionalTranslationEnergy s f := by
  apply lintegral_congr
  intro t
  by_cases ht : t = 0
  · simp [ht, circleTranslation_zero]
  · rw [realFractionalKernel, fractionalTranslationKernel, ENNReal.ofReal_rpow_of_pos (abs_pos.mpr ht)]

/-- The full displacement energy is controlled by central fractional energy and the `L²` term. -/
theorem translationEnergy_realFractionalKernel_le {s : ℝ} (hs : 0 < s) (f : CircleL2) :
    translationEnergy volume (realFractionalKernel s) f ≤
      fractionalTranslationEnergy s f + ENNReal.ofReal (4 / s * ‖f‖ ^ 2) := by
  have hb (t : ℝ) : ENNReal.ofReal (‖circleTranslation t f - f‖ ^ 2) ≤ ENNReal.ofReal (4 * ‖f‖ ^ 2) := by
    apply ENNReal.ofReal_le_ofReal
    have h := sq_le_sq₀ (norm_nonneg _) (by positivity) |>.mpr (norm_circleTranslation_sub_le t f)
    nlinarith
  have ht : (∫⁻ t : ℝ in (Icc (-1) 1)ᶜ, realFractionalKernel s t * ENNReal.ofReal (‖circleTranslation t f - f‖ ^ 2)) ≤
      ENNReal.ofReal (4 / s * ‖f‖ ^ 2) := by
    calc
      _ ≤ ∫⁻ t : ℝ in (Icc (-1) 1)ᶜ, realFractionalKernel s t * ENNReal.ofReal (4 * ‖f‖ ^ 2) :=
        lintegral_mono (fun t => mul_le_mul' le_rfl (hb t))
      _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_realFractionalKernel_tail hs,
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / s)]
        congr 1
        ring
  change (∫⁻ t : ℝ, realFractionalKernel s t * ENNReal.ofReal (‖circleTranslation t f - f‖ ^ 2)) ≤ _
  rw [← lintegral_add_compl _ measurableSet_Icc]
  change translationEnergy (volume.restrict (Icc (-1) 1)) (realFractionalKernel s) f + _ ≤ _
  rw [translationEnergy_realFractionalKernel_central]
  exact add_le_add le_rfl ht

/-- The reverse physical comparison; no finite-energy assumption is needed. -/
theorem fractionalIntervalEnergy_le_periodic {s : ℝ} (hs : 0 < s) (f : CircleL2) :
    fractionalIntervalEnergy s 2 (circlePullback f) ≤
      2 * (fractionalTranslationEnergy s f + ENNReal.ofReal (4 / s * ‖f‖ ^ 2)) :=
  (fractionalIntervalEnergy_le_full_translation s f).trans
    (mul_le_mul' le_rfl (translationEnergy_realFractionalKernel_le hs f))

/-- Periodic fractional regularity restricts to finite intrinsic interval energy. -/
theorem fractionalIntervalEnergy_lt_top_of_periodic {s : ℝ} (hs : 0 < s)
    (f : CircleL2) (hf : HasFractionalPeriodicRegularity s f) :
    fractionalIntervalEnergy s 2 (circlePullback f) < ⊤ :=
  (fractionalIntervalEnergy_le_periodic hs f).trans_lt
    (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hf, ENNReal.ofReal_lt_top⟩))

end NLS.Fourier
