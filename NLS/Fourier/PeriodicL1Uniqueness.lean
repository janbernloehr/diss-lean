import NLS.Fourier.PeriodicL1Fourier
import NLS.Fourier.ComplexMeasureContinuousIntegral
import Mathlib.MeasureTheory.VectorMeasure.WithDensity
/-!
# Uniqueness of integrable periodic representatives

Continuous tests separate integrable densities on compact metrizable spaces:
positive and negative density measures coincide only when the real density
vanishes almost everywhere. Applying this to real and imaginary parts, then
using density of the original smooth tests, proves uniqueness of the physical
Lᵖ representative, including p = 1 and p = ∞.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal CompactlySupported ZeroAtInfty
namespace NLS.Fourier
variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X]
  {μ : Measure X}

/-- Real integrable densities are separated by continuous real tests. -/
theorem ae_eq_zero_of_integral_mul_continuous_eq_zero_real
    {f : X → ℝ} (hf : Integrable f μ)
    (h : ∀ g : C(X,ℝ), ∫ x, f x * g x ∂μ = 0) : f =ᵐ[μ] 0 := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (f x))
  let ξ := μ.withDensity (fun x => ENNReal.ofReal (-f x))
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hf.2
  let : IsFiniteMeasure ξ := isFiniteMeasure_withDensity_ofReal hf.neg.2
  have he : ν = ξ := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    change (∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (f x))) =
      ∫ x, g x ∂μ.withDensity (fun x => ENNReal.ofReal (-f x))
    rw [integral_withDensity_eq_integral_toReal_smul₀ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal (by simp),
      integral_withDensity_eq_integral_toReal_smul₀ (show AEMeasurable (fun x => ENNReal.ofReal (-f x)) μ from hf.neg.aestronglyMeasurable.aemeasurable.ennreal_ofReal) (by simp)]
    apply sub_eq_zero.mp
    rw [← integral_sub]
    · convert h g.toContinuousMap using 1
      congr 1
      funext x
      simp only [smul_eq_mul,ENNReal.toReal_ofReal',← sub_mul]
      congr 1
      rcases le_total 0 (f x) with hx | hx
      · simp [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
      · simp [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
    · exact hf.pos_part.mul_bdd g.continuous.aestronglyMeasurable
        (ae_of_all _ g.toContinuousMap.norm_coe_le_norm)
    · exact hf.neg.pos_part.mul_bdd g.continuous.aestronglyMeasurable
        (ae_of_all _ g.toContinuousMap.norm_coe_le_norm)
  apply hf.ae_eq_of_withDensityᵥ_eq (integrable_zero X ℝ μ)
  rw [withDensityᵥ_eq_withDensity_pos_part_sub_withDensity_neg_part hf]
  change ν.toSignedMeasure - ξ.toSignedMeasure = _
  rw [Measure.toSignedMeasure_eq_toSignedMeasure_iff.mpr he,sub_self]
  simp

/-- Complex integrable densities are separated by continuous complex tests. -/
theorem ae_eq_zero_of_integral_mul_continuous_eq_zero_complex
    {f : X → ℂ} (hf : Integrable f μ)
    (h : ∀ g : C(X,ℂ), ∫ x, f x * g x ∂μ = 0) : f =ᵐ[μ] 0 := by
  have hr : (fun x => (f x).re) =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_integral_mul_continuous_eq_zero_real hf.re
    intro g
    have hi := hf.mul_bdd (realContinuousTest g).continuous.aestronglyMeasurable
      (ae_of_all _ (realContinuousTest g).norm_coe_le_norm)
    have he := congrArg Complex.re (h (realContinuousTest g))
    have he := (integral_re hi).trans he
    simpa [realContinuousTest,Complex.mul_re] using he
  have hi : (fun x => (f x).im) =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_integral_mul_continuous_eq_zero_real hf.im
    intro g
    have hi := hf.mul_bdd (realContinuousTest g).continuous.aestronglyMeasurable
      (ae_of_all _ (realContinuousTest g).norm_coe_le_norm)
    have he := congrArg Complex.im (h (realContinuousTest g))
    have he := (integral_im hi).trans he
    simpa [realContinuousTest,Complex.mul_im] using he
  filter_upwards [hr,hi] with x hx hy
  exact Complex.ext hx hy

namespace SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]

theorem ofCircleL1_congr {f g : AddCircle L → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (hg : Integrable g AddCircle.haarAddCircle)
    (h : f =ᵐ[AddCircle.haarAddCircle] g) : ofCircleL1 f hf = ofCircleL1 g hg := by
  ext t
  apply integral_congr_ae
  filter_upwards [h] with x hx
  rw [hx]

theorem ofCircleL1_eq_zero_iff {f : AddCircle L → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) :
    ofCircleL1 f hf = 0 ↔ f =ᵐ[AddCircle.haarAddCircle] 0 := by
  constructor
  · intro h
    apply ae_eq_zero_of_integral_mul_continuous_eq_zero_complex hf
    have he : circleL1Functional f hf = 0 := by
      apply DFunLike.coe_injective
      apply denseRange_toContinuousCLM.equalizer (circleL1Functional f hf).continuous
        (0 : C(AddCircle L,ℂ) →L[ℂ] ℂ).continuous
      funext t
      exact congrArg (fun u : Distribution L => u t) h
    intro g
    exact congrArg (fun F : C(AddCircle L,ℂ) →L[ℂ] ℂ => F g) he
  · intro h
    ext t
    change (∫ x, f x * toContinuousCLM t x ∂AddCircle.haarAddCircle) = 0
    calc
      _ = ∫ x, (0:ℂ) ∂AddCircle.haarAddCircle := by
        apply integral_congr_ae
        filter_upwards [h] with x hx
        simp [hx]
      _ = 0 := integral_zero _ _

/-- Original periodic distributions distinguish L¹ functions modulo a.e. equality. -/
theorem ofCircleL1_eq_iff {f g : AddCircle L → ℂ}
    (hf : Integrable f AddCircle.haarAddCircle) (hg : Integrable g AddCircle.haarAddCircle) :
    ofCircleL1 f hf = ofCircleL1 g hg ↔ f =ᵐ[AddCircle.haarAddCircle] g := by
  constructor
  · intro h
    have he : ofCircleL1 (f-g) (hf.sub hg) = 0 := by
      ext t
      change (∫ x, (f x-g x)*toContinuousCLM t x ∂AddCircle.haarAddCircle) = 0
      simp_rw [sub_mul]
      rw [integral_sub
        (hf.mul_bdd (toContinuousCLM t).continuous.aestronglyMeasurable (ae_of_all _ (toContinuousCLM t).norm_coe_le_norm))
        (hg.mul_bdd (toContinuousCLM t).continuous.aestronglyMeasurable (ae_of_all _ (toContinuousCLM t).norm_coe_le_norm))]
      exact sub_eq_zero.mpr (congrArg (fun u : Distribution L => u t) h)
    filter_upwards [(ofCircleL1_eq_zero_iff (hf.sub hg)).mp he] with x hx
    exact sub_eq_zero.mp hx
  · exact ofCircleL1_congr hf hg

/-- Faithful realization of every Banach Lᵖ quotient in the original periodic dual. -/
theorem ofCircleLp_injective {r : ℝ≥0∞} [Fact (1 ≤ r)] :
    Function.Injective (fun f : Lp ℂ r (AddCircle.haarAddCircle (T := L)) =>
      ofCircleL1 f ((Lp.memLp f).integrable (Fact.out : 1 ≤ r))) := by
  intro f g h
  apply Lp.ext
  exact (ofCircleL1_eq_iff _ _).mp h

end SmoothPeriodicTest.Distribution
variable {L : ℝ} [Fact (0 < L)]

/-- All Fourier coefficients uniquely determine an Lᵖ equivalence class. -/
theorem circleLp_fourierCoeff_injective {r : ℝ≥0∞} [Fact (1 ≤ r)] :
    Function.Injective (fun f : Lp ℂ r (AddCircle.haarAddCircle (T := L)) => fourierCoeff f) := by
  intro f g h
  apply SmoothPeriodicTest.Distribution.ofCircleLp_injective
  apply SmoothPeriodicTest.Distribution.ext_coefficients
  intro n
  simpa only [SmoothPeriodicTest.Distribution.ofCircleL1_coefficient] using congrFun h n

/-- The actual L¹ → c₀ Fourier map is injective. -/
theorem circleL1Fourier_injective : Function.Injective (circleL1Fourier (L := L)) := by
  intro f g h
  apply circleLp_fourierCoeff_injective
  funext n
  simpa only [circleL1Fourier_apply] using congrArg (fun a : C₀(ℤ,ℂ) => a n) h

end NLS.Fourier
