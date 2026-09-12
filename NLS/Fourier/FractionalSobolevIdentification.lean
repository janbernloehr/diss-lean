import NLS.SequenceSpaces.SobolevHomogeneous
import NLS.Fourier.FractionalSpectralBounds

/-!
# Physical periodic fractional Sobolev identification

For `0 < s < 1`, finite physical translation energy is exactly the range of
weighted Hilbert Fourier synthesis. Both inverse identities and quantitative
energy bounds retain the unweighted term controlling constant functions.
This is a periodic statement; no nonperiodic interval boundary estimate is used.
-/

noncomputable section
open scoped ENNReal
namespace NLS.Fourier

/-- Hilbert synthesis of nonnegative Sobolev coefficients. -/
def sobolevL2Synthesis {s : ℝ} (hs : 0 ≤ s) :
    WeightedCoeff (Weight.sobolev s) 2 →L[ℂ] CircleL2 :=
  l2Synthesis.toContinuousLinearEquiv.toContinuousLinearMap.comp (WeightedCoeff.sobolevToL2 hs)

@[simp] theorem fourierCoeff_sobolevL2Synthesis {s : ℝ} (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) 2) (n : ℤ) :
    fourierCoeff (sobolevL2Synthesis hs a) n = a.val n := by
  change fourierCoeff (l2Synthesis (WeightedCoeff.sobolevToL2 hs a)) n = _
  rw [fourierCoeff_l2Synthesis, WeightedCoeff.sobolevToL2_apply]

@[simp] theorem norm_sobolevL2Synthesis {s : ℝ} (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    ‖sobolevL2Synthesis hs a‖ = ‖WeightedCoeff.sobolevToL2 hs a‖ := norm_l2Synthesis _

theorem norm_sobolevL2Synthesis_le {s : ℝ} (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) 2) : ‖sobolevL2Synthesis hs a‖ ≤ ‖a‖ :=
  (norm_sobolevL2Synthesis hs a).trans_le (WeightedCoeff.norm_sobolevToL2_le hs a)

theorem sobolevL2Synthesis_injective {s : ℝ} (hs : 0 ≤ s) :
    Function.Injective (sobolevL2Synthesis hs) := by
  intro a b h
  apply Subtype.ext
  funext n
  simpa only [fourierCoeff_sobolevL2Synthesis] using congrArg (fun f : CircleL2 => fourierCoeff f n) h

/-- Physical fractional regularity is the project's inhomogeneous weighted square summability. -/
theorem hasFractionalPeriodicRegularity_iff_memlp {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) : HasFractionalPeriodicRegularity s f ↔
      Memℓp (fun n => (Weight.sobolev s n : ℂ) * fourierCoeff f n) 2 := by
  rw [hasFractionalPeriodicRegularity_iff_summable hs hs₁]
  simpa only [fourierBasis_repr] using
    (Coeff.memlp_sobolev_iff_homogeneous hs.le (fourierBasis.repr f)).symm

theorem hasFractionalPeriodicRegularity_sobolevL2Synthesis {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    HasFractionalPeriodicRegularity s (sobolevL2Synthesis hs.le a) := by
  rw [hasFractionalPeriodicRegularity_iff_memlp hs hs₁]
  simpa only [fourierCoeff_sobolevL2Synthesis] using! a.property

/-- The actual Fourier coefficients of a physically regular periodic function. -/
def fractionalSobolevCoefficients {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) (hf : HasFractionalPeriodicRegularity s f) : WeightedCoeff (Weight.sobolev s) 2 :=
  ⟨fourierCoeff f, (hasFractionalPeriodicRegularity_iff_memlp hs hs₁ f).mp hf⟩

@[simp] theorem fractionalSobolevCoefficients_apply {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) (hf : HasFractionalPeriodicRegularity s f) (n : ℤ) :
    (fractionalSobolevCoefficients hs hs₁ f hf).val n = fourierCoeff f n := rfl

/-- Fourier synthesis reconstructs the original physical `L²` element. -/
@[simp] theorem sobolevL2Synthesis_fractionalSobolevCoefficients {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) (hf : HasFractionalPeriodicRegularity s f) :
    sobolevL2Synthesis hs.le (fractionalSobolevCoefficients hs hs₁ f hf) = f := by
  apply fourierBasis.repr.injective
  ext n
  simp only [fourierBasis_repr, fourierCoeff_sobolevL2Synthesis, fractionalSobolevCoefficients_apply]

@[simp] theorem fractionalSobolevCoefficients_sobolevL2Synthesis {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    fractionalSobolevCoefficients hs hs₁ (sobolevL2Synthesis hs.le a)
      (hasFractionalPeriodicRegularity_sobolevL2Synthesis hs hs₁ a) = a := by
  apply Subtype.ext
  funext n
  simp only [fractionalSobolevCoefficients_apply, fourierCoeff_sobolevL2Synthesis]

/-- Intrinsic physical regularity is equivalent to a unique weighted representation. -/
theorem hasFractionalPeriodicRegularity_iff_existsUnique {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (f : CircleL2) : HasFractionalPeriodicRegularity s f ↔
      ∃! a : WeightedCoeff (Weight.sobolev s) 2, sobolevL2Synthesis hs.le a = f := by
  constructor
  · intro hf
    refine ⟨fractionalSobolevCoefficients hs hs₁ f hf,
      sobolevL2Synthesis_fractionalSobolevCoefficients hs hs₁ f hf, ?_⟩
    intro a ha
    apply sobolevL2Synthesis_injective hs.le
    rw [ha, sobolevL2Synthesis_fractionalSobolevCoefficients]
  · rintro ⟨a, rfl, _⟩
    exact hasFractionalPeriodicRegularity_sobolevL2Synthesis hs hs₁ a

/-- The homogeneous energy of a weighted representative is a convergent real sum. -/
theorem homogeneousFourierEnergy_sobolevL2Synthesis {s : ℝ} (hs : 0 ≤ s)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    homogeneousFourierEnergy s (sobolevL2Synthesis hs a) =
      ENNReal.ofReal (∑' n : ℤ, |(n : ℝ)| ^ (2 * s) * ‖a.val n‖ ^ 2) := by
  simp only [homogeneousFourierEnergy, fourierCoeff_sobolevL2Synthesis]
  exact (ENNReal.ofReal_tsum_of_nonneg (fun _ => by positivity)
    (WeightedCoeff.summable_homogeneous hs a)).symm

/-- The physical fractional energy is controlled by the weighted Sobolev norm. -/
theorem fractionalTranslationEnergy_sobolevL2Synthesis_le {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    fractionalTranslationEnergy s (sobolevL2Synthesis hs.le a) ≤
      ENNReal.ofReal (fractionalUpperConstant s * ‖a‖ ^ 2) := by
  refine (fractionalTranslationEnergy_bounds hs hs₁ _).2.trans ?_
  rw [homogeneousFourierEnergy_sobolevL2Synthesis,
    ENNReal.ofReal_mul (fractionalUpperConstant_pos hs hs₁).le]
  exact mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal (WeightedCoeff.homogeneous_tsum_le_norm_sq hs.le a))

/-- The `L²` term and homogeneous energy control the weighted norm, including the zero mode. -/
theorem sobolev_norm_sq_le_physical_energy {s : ℝ} (hs : 0 < s) (hs₁ : s < 1)
    (a : WeightedCoeff (Weight.sobolev s) 2) :
    ENNReal.ofReal (fractionalLowerConstant s * ‖a‖ ^ 2) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * s)) *
        (ENNReal.ofReal (fractionalLowerConstant s * ‖sobolevL2Synthesis hs.le a‖ ^ 2) +
          fractionalTranslationEnergy s (sobolevL2Synthesis hs.le a)) := by
  have hc := (fractionalLowerConstant_pos hs hs₁).le
  have hh := WeightedCoeff.norm_sq_le_homogeneous hs.le a
  have h := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hh hc)
  have hn : 0 ≤ ‖WeightedCoeff.sobolevToL2 hs.le a‖ ^ 2 := sq_nonneg _
  have hsum : 0 ≤ ∑' n : ℤ, |(n : ℝ)| ^ (2 * s) * ‖a.val n‖ ^ 2 :=
    tsum_nonneg (fun _ => by positivity)
  calc
    ENNReal.ofReal (fractionalLowerConstant s * ‖a‖ ^ 2) ≤ _ := h
    _ = ENNReal.ofReal ((2 : ℝ) ^ (2 * s)) *
        (ENNReal.ofReal (fractionalLowerConstant s * ‖sobolevL2Synthesis hs.le a‖ ^ 2) +
          ENNReal.ofReal (fractionalLowerConstant s) *
            homogeneousFourierEnergy s (sobolevL2Synthesis hs.le a)) := by
      simp only [homogeneousFourierEnergy_sobolevL2Synthesis, norm_sobolevL2Synthesis,
        ENNReal.ofReal_mul hc, ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _),
        ENNReal.ofReal_add hn hsum]
      ring
    _ ≤ _ := mul_le_mul' le_rfl (add_le_add_right (fractionalTranslationEnergy_bounds hs hs₁ _).1 _)

end NLS.Fourier
