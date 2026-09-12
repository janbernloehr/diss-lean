import NLS.Fourier.ContinuousSynthesis
import NLS.SequenceSpaces.SobolevConstant
import NLS.SequenceSpaces.Reflection
import NLS.ZakharovShabat.Domain

/-!
# Continuous representatives of one-derivative coefficients

For every finite Banach exponent, the weighted domain embeds continuously into
continuous functions on the period-two circle. At exponent two this representative
agrees with the Hilbert-space Fourier inverse. This is a prerequisite for the
classical Sobolev identification; no weak-derivative identification is asserted here.
-/

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace NLS.Fourier

/-- The normalized period-two Fourier inverse on the whole Hilbert space. -/
def l2Synthesis : Coeff 2 ≃ₗᵢ[ℂ] Lp ℂ 2 (AddCircle.haarAddCircle (T := (2 : ℝ))) :=
  fourierBasis.repr.symm

@[simp] theorem fourierCoeff_l2Synthesis (a : Coeff 2) (n : ℤ) :
    fourierCoeff (l2Synthesis a) n = a n := by
  rw [← fourierBasis_repr]
  exact congrArg (fun b : Coeff 2 => b n) (fourierBasis.repr.apply_symm_apply a)

@[simp] theorem norm_l2Synthesis (a : Coeff 2) : ‖l2Synthesis a‖ = ‖a‖ :=
  l2Synthesis.norm_map a

variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- The continuous representative of a one-derivative coefficient sequence. -/
def sobolevSynthesis (hp : p ≠ ⊤) :
    WeightedCoeff (Weight.sobolev 1) p →L[ℂ] C(AddCircle (2 : ℝ), ℂ) :=
  continuousSynthesisCLM.comp (WeightedCoeff.sobolevToL1CLM p hp)

/-- Uniform control of the representative by its weighted coefficient norm. -/
theorem norm_sobolevSynthesis_le (hp : p ≠ ⊤) (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevSynthesis hp a‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖a‖ :=
  (norm_continuousSynthesis_le _).trans (WeightedCoeff.norm_sobolevToL1CLM_le p hp a)

/-- The explicit Appendix A bound for the uniform representative. -/
theorem norm_sobolevSynthesis_le_two_mul (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevSynthesis hp a‖ ≤ (2 * p.toReal) * ‖a‖ :=
  (norm_sobolevSynthesis_le hp a).trans
    (mul_le_mul_of_nonneg_right (WeightedCoeff.sobolevEmbeddingConstant_le_two_mul p hp)
      (norm_nonneg a))

/-- The weighted Fourier series converges in the uniform norm. -/
theorem hasSum_sobolevSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    HasSum (fun n : ℤ => a.val n • fourier n) (sobolevSynthesis hp a) := by
  simpa only [WeightedCoeff.sobolevToL1CLM_apply, sobolevSynthesis,
    ContinuousLinearMap.comp_apply, continuousSynthesisCLM_apply] using
    hasSum_continuousSynthesis (WeightedCoeff.sobolevToL1CLM p hp a)

/-- Finite weighted truncations approximate the representative uniformly. -/
theorem tendsto_sobolevSynthesis_truncate (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    Filter.Tendsto
      (fun s : Finset ℤ => sobolevSynthesis hp (WeightedCoeff.truncate (Weight.sobolev 1) p s a))
      Filter.atTop (nhds (sobolevSynthesis hp a)) :=
  ((sobolevSynthesis hp).continuous.tendsto a).comp
    (WeightedCoeff.tendsto_truncate (Weight.sobolev 1) p hp a)

@[simp] theorem fourierCoeff_sobolevSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (n : ℤ) :
    fourierCoeff (sobolevSynthesis hp a) n = a.val n := by
  change fourierCoeff (continuousSynthesis (WeightedCoeff.sobolevToL1CLM p hp a)) n = _
  simp

@[simp] theorem periodTwoCoefficient_sobolevSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (n : ℤ) :
    periodTwoCoefficient (fun x : ℝ => sobolevSynthesis hp a (x : AddCircle (2 : ℝ))) n =
      a.val n := by
  rw [periodTwoCoefficient_circle, fourierCoeff_sobolevSynthesis]

theorem sobolevSynthesis_injective (hp : p ≠ ⊤) : Function.Injective (sobolevSynthesis hp) := by
  intro a b h
  apply Subtype.ext
  funext n
  simpa only [fourierCoeff_sobolevSynthesis] using
    congrArg (fun f : C(AddCircle (2 : ℝ), ℂ) => fourierCoeff f n) h

/-- A continuous representative with the prescribed coefficients is unique. -/
theorem eq_sobolevSynthesis_of_fourierCoeff (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (f : C(AddCircle (2 : ℝ), ℂ))
    (hf : ∀ n, fourierCoeff f n = a.val n) : f = sobolevSynthesis hp a := by
  apply continuousFourierCLM_injective
  ext n
  simp only [continuousFourierCLM_apply, fourierCoeff_sobolevSynthesis, hf]

/-- The representative on the real line is continuous. -/
@[fun_prop] theorem continuous_sobolevSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    Continuous (fun x : ℝ => sobolevSynthesis hp a (x : AddCircle (2 : ℝ))) :=
  (sobolevSynthesis hp a).continuous.comp continuous_quotient_mk'

/-- The full period is two; no period-one condition is imposed. -/
theorem periodic_sobolevSynthesis (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    Function.Periodic (fun x : ℝ => sobolevSynthesis hp a (x : AddCircle (2 : ℝ))) 2 := by
  intro x
  dsimp only
  rw [AddCircle.coe_add_period]

/-- The value of a weighted single mode, in the physical normalization. -/
@[simp] theorem sobolevSynthesis_scalarMode (hp : p ≠ ⊤) (n : ℤ) (c : ℂ) (x : ℝ) :
    sobolevSynthesis hp (ZakharovShabat.scalarMode n c) (x : AddCircle (2 : ℝ)) =
      c * wave n x := by
  have h : WeightedCoeff.sobolevToL1CLM p hp (ZakharovShabat.scalarMode n c) =
      lp.single 1 n c := by
    ext k
    simp [ZakharovShabat.scalarMode_apply, lp.single_apply, Pi.single_apply]
  change continuousSynthesis (WeightedCoeff.sobolevToL1CLM p hp
    (ZakharovShabat.scalarMode n c)) (x : AddCircle (2 : ℝ)) = _
  rw [h, continuousSynthesis_single]
  simp only [ContinuousMap.smul_apply, smul_eq_mul, fourier_two_eq_wave]

/-- Evaluation is a bounded trace functional, including at the interval endpoints. -/
def sobolevTrace (hp : p ≠ ⊤) (x : ℝ) : WeightedCoeff (Weight.sobolev 1) p →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (x : AddCircle (2 : ℝ))).comp (sobolevSynthesis hp)

@[simp] theorem sobolevTrace_apply (hp : p ≠ ⊤) (x : ℝ)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevTrace hp x a = sobolevSynthesis hp a (x : AddCircle (2 : ℝ)) := rfl

theorem norm_sobolevTrace_apply_le (hp : p ≠ ⊤) (x : ℝ)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    ‖sobolevTrace hp x a‖ ≤ WeightedCoeff.sobolevEmbeddingConstant p hp * ‖a‖ :=
  ((sobolevSynthesis hp a).norm_coe_le_norm _).trans (norm_sobolevSynthesis_le hp a)

/-- Frequency reversal realizes the physical reflection about the half period. -/
theorem sobolevSynthesis_reflection (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (x : ℝ) :
    sobolevSynthesis hp (WeightedCoeff.reflection 1 a) (x : AddCircle (2 : ℝ)) =
      sobolevSynthesis hp a ((2 - x : ℝ) : AddCircle (2 : ℝ)) := by
  change continuousSynthesis (WeightedCoeff.sobolevToL1CLM p hp
    (WeightedCoeff.reflection 1 a)) (x : AddCircle (2 : ℝ)) =
      continuousSynthesis (WeightedCoeff.sobolevToL1CLM p hp a)
        ((2 - x : ℝ) : AddCircle (2 : ℝ))
  simp only [continuousSynthesis_apply, WeightedCoeff.sobolevToL1CLM_apply,
    WeightedCoeff.reflection_apply, wave_reflect]
  rw [← (Equiv.neg ℤ).tsum_eq (fun n : ℤ => a.val n * wave (-n) x)]
  simp

/-- Reflection fixes the left endpoint trace. -/
@[simp] theorem sobolevTrace_reflection_zero (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevTrace hp 0 (WeightedCoeff.reflection 1 a) = sobolevTrace hp 0 a := by
  simp only [sobolevTrace_apply, sobolevSynthesis_reflection, sub_zero]
  have h := periodic_sobolevSynthesis hp a 0
  simpa using h

/-- Reflection fixes the right endpoint of the original interval. -/
@[simp] theorem sobolevTrace_reflection_one (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) :
    sobolevTrace hp 1 (WeightedCoeff.reflection 1 a) = sobolevTrace hp 1 a := by
  simp only [sobolevTrace_apply, sobolevSynthesis_reflection, show (2 : ℝ) - 1 = 1 by norm_num]

/-- Odd reflection symmetry forces both original interval endpoint values to vanish. -/
theorem sobolevTrace_eq_zero_of_odd (hp : p ≠ ⊤)
    (a : WeightedCoeff (Weight.sobolev 1) p) (ha : WeightedCoeff.reflection 1 a = -a) :
    sobolevTrace hp 0 a = 0 ∧ sobolevTrace hp 1 a = 0 := by
  have h0 := sobolevTrace_reflection_zero hp a
  have h1 := sobolevTrace_reflection_one hp a
  rw [ha, map_neg] at h0 h1
  constructor
  · linear_combination - (1 / 2 : ℂ) * h0
  · linear_combination - (1 / 2 : ℂ) * h1

/-- The continuous and Hilbert-space realizations agree at exponent two. -/
theorem toLp_sobolevSynthesis (a : ZakharovShabat.ScalarDomain 2) :
    ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (sobolevSynthesis (by simp) a) =
      l2Synthesis (ZakharovShabat.scalarInclusion a) := by
  apply fourierBasis.repr.injective
  ext n
  rw [fourierBasis_repr, fourierCoeff_toLp, fourierCoeff_sobolevSynthesis,
    fourierBasis_repr, fourierCoeff_l2Synthesis, ZakharovShabat.scalarInclusion_apply]

/-- The continuous function has the same normalized `L²` norm as its raw coefficients. -/
theorem norm_toLp_sobolevSynthesis (a : ZakharovShabat.ScalarDomain 2) :
    ‖ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ (sobolevSynthesis (by simp) a)‖ =
      ‖ZakharovShabat.scalarInclusion a‖ := by
  rw [toLp_sobolevSynthesis, norm_l2Synthesis]

end NLS.Fourier
