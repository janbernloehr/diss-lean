import NLS.ComplexAnalysis.SineExteriorKernelCorrection
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integral mixtures of exterior cosine kernels

Fubini extends the correction inequality from finite sums to kernel
integrals. An integrable exterior-distance majorant supplies continuity
of the profile and absolute integrability of the product integrand.
Measurability, positivity, and integrability requirements remain explicit.
-/

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace NLS.ComplexAnalysis
open Set MeasureTheory

/-- Positive exterior kernel integrals have the required linear correction moment.
The product integrability hypothesis justifies Fubini across both variables. -/
theorem sine_integral_kernel_correction_nonneg {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (c s : α → ℝ)
    (hc : ∀ᵐ a ∂μ, 0 ≤ c a) (hs : ∀ᵐ a ∂μ, 1 < |s a|)
    (hint : Integrable (fun z : ℝ × α =>
      (2*(Real.sin z.1)^4-(Real.sin z.1)^2)*(c z.2/|s z.2-Real.cos z.1|))
      ((volume.restrict (Ioc (0:ℝ) Real.pi)).prod μ)) :
    0 ≤ ∫ x in (0:ℝ)..Real.pi,
      (2*(Real.sin x)^4-(Real.sin x)^2)*(∫ a, c a/|s a-Real.cos x| ∂μ) := by
  let w : ℝ → ℝ := fun x => 2*(Real.sin x)^4-(Real.sin x)^2
  have he : (∫ x in (0:ℝ)..Real.pi, w x*(∫ a, c a/|s a-Real.cos x| ∂μ)) =
      ∫ a, c a*(∫ x in (0:ℝ)..Real.pi, w x/|s a-Real.cos x|) ∂μ := by
    rw [intervalIntegral.integral_of_le Real.pi_pos.le]
    calc
      _ = ∫ x in Ioc (0:ℝ) Real.pi, ∫ a, w x*(c a/|s a-Real.cos x|) ∂μ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (integral_const_mul (w x) _).symm)
      _ = ∫ a, (∫ x in Ioc (0:ℝ) Real.pi, w x*(c a/|s a-Real.cos x|)) ∂μ :=
        integral_integral_swap hint
      _ = _ := by
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro a
        dsimp only
        rw [intervalIntegral.integral_of_le Real.pi_pos.le,← integral_const_mul]
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro x
        ring
  change 0 ≤ ∫ x in (0:ℝ)..Real.pi, w x*(∫ a, c a/|s a-Real.cos x| ∂μ)
  rw [he]
  apply integral_nonneg_of_ae
  filter_upwards [hc,hs] with a hca hsa
  exact mul_nonneg hca (sine_correction_exterior_kernel_integral_nonneg (s a) hsa)

/-- The sharp cubic ratio holds for a continuous positive integral of exterior kernels. -/
theorem sine_integral_kernel_profile_cubic {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (c s : α → ℝ)
    (hc : ∀ᵐ a ∂μ, 0 ≤ c a) (hs : ∀ᵐ a ∂μ, 1 < |s a|)
    (hV : Continuous (fun x : ℝ => ∫ a, c a/|s a-Real.cos x| ∂μ))
    (hint : Integrable (fun z : ℝ × α =>
      (2*(Real.sin z.1)^4-(Real.sin z.1)^2)*(c z.2/|s z.2-Real.cos z.1|))
      ((volume.restrict (Ioc (0:ℝ) Real.pi)).prod μ)) :
    let V : ℝ → ℝ := fun x => ∫ a, c a/|s a-Real.cos x| ∂μ
    3*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x))^2 ≤
      2*Real.pi*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) := by
  apply sine_corrected_profile_cubic _ hV
  · intro x _
    apply integral_nonneg_of_ae
    filter_upwards [hc] with a ha
    exact div_nonneg ha (abs_nonneg _)
  · exact sine_integral_kernel_correction_nonneg μ c s hc hs hint

end NLS.ComplexAnalysis

namespace NLS.ComplexAnalysis
open Set MeasureTheory

/-- The distance from an exterior pole gives one integrable majorant for every angle. -/
theorem exterior_cosine_kernel_norm_le (c s x : ℝ) (hc : 0 ≤ c) (hs : 1 < |s|) :
    ‖c/|s-Real.cos x|‖ ≤ c/(|s|-1) := by
  have hd : |s|-1 ≤ |s-Real.cos x| := by
    have hx : |Real.cos x| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩
    linarith [abs_sub_abs_le_abs_sub s (Real.cos x)]
  rw [Real.norm_eq_abs,abs_of_nonneg (div_nonneg hc (abs_nonneg _))]
  exact div_le_div_of_nonneg_left hc (sub_pos.mpr hs) hd

/-- An integrable exterior-distance majorant makes the kernel profile continuous. -/
theorem continuous_integral_exterior_cosine_kernel {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (c s : α → ℝ) (hcm : Measurable c) (hsm : Measurable s)
    (hc : ∀ a, 0 ≤ c a) (hs : ∀ a, 1 < |s a|)
    (hint : Integrable (fun a => c a/(|s a|-1)) μ) :
    Continuous (fun x : ℝ => ∫ a, c a/|s a-Real.cos x| ∂μ) := by
  apply continuous_of_dominated (bound := fun a => c a/(|s a|-1))
  · intro x
    exact (hcm.div ((hsm.sub measurable_const).norm)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun a => exterior_cosine_kernel_norm_le (c a) (s a) x (hc a) (hs a))
  · exact hint
  · apply Filter.Eventually.of_forall
    intro a
    apply continuous_const.div ((continuous_const.sub Real.continuous_cos).abs)
    intro x
    apply ne_of_gt
    apply abs_pos.mpr
    intro hz
    have he := sub_eq_zero.mp hz
    change s a = Real.cos x at he
    have ha := hs a
    rw [he] at ha
    exact (not_lt_of_ge (abs_le.mpr ⟨Real.neg_one_le_cos x,Real.cos_le_one x⟩)) ha

/-- The same majorant justifies the product integral used in the correction estimate. -/
theorem integrable_sine_exterior_kernel_correction {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (c s : α → ℝ) (hcm : Measurable c) (hsm : Measurable s)
    (hc : ∀ a, 0 ≤ c a) (hs : ∀ a, 1 < |s a|)
    (hint : Integrable (fun a => c a/(|s a|-1)) μ) :
    Integrable (fun z : ℝ × α =>
      (2*(Real.sin z.1)^4-(Real.sin z.1)^2)*(c z.2/|s z.2-Real.cos z.1|))
      ((volume.restrict (Ioc (0:ℝ) Real.pi)).prod μ) := by
  have hb := (hint.const_mul 3).comp_snd (volume.restrict (Ioc (0:ℝ) Real.pi))
  apply hb.mono'
  · have hsin := Real.continuous_sin.measurable.comp (measurable_fst : Measurable (Prod.fst : ℝ × α → ℝ))
    have hcos := Real.continuous_cos.measurable.comp (measurable_fst : Measurable (Prod.fst : ℝ × α → ℝ))
    exact (((hsin.pow_const 4).const_mul 2).sub (hsin.pow_const 2)).mul
      ((hcm.comp measurable_snd).div (((hsm.comp measurable_snd).sub hcos).norm)) |>.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro z
    have hsin : |Real.sin z.1| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin z.1,Real.sin_le_one z.1⟩
    have h2 : (Real.sin z.1)^2 ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left hsin (abs_nonneg (Real.sin z.1))
      nlinarith [sq_abs (Real.sin z.1)]
    have h2n : 0 ≤ (Real.sin z.1)^2 := sq_nonneg _
    have h4 : (Real.sin z.1)^4 ≤ 1 := by
      nlinarith [mul_nonneg h2n (show 0 ≤ 1-(Real.sin z.1)^2 by linarith)]
    have hw : ‖2*(Real.sin z.1)^4-(Real.sin z.1)^2‖ ≤ (3:ℝ) := by
      rw [Real.norm_eq_abs]
      exact abs_le.mpr ⟨by nlinarith [sq_nonneg ((Real.sin z.1)^2)],by nlinarith⟩
    rw [norm_mul]
    exact mul_le_mul hw (exterior_cosine_kernel_norm_le (c z.2) (s z.2) z.1 (hc z.2) (hs z.2))
      (norm_nonneg _) (by norm_num)

/-- Measurable positive exterior kernels with one integrable majorant have the sharp ratio. -/
theorem sine_dominated_exterior_kernel_profile_cubic {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ] (c s : α → ℝ) (hcm : Measurable c) (hsm : Measurable s)
    (hc : ∀ a, 0 ≤ c a) (hs : ∀ a, 1 < |s a|)
    (hint : Integrable (fun a => c a/(|s a|-1)) μ) :
    let V : ℝ → ℝ := fun x => ∫ a, c a/|s a-Real.cos x| ∂μ
    3*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^2*(1+V x))^2 ≤
      2*Real.pi*(∫ x in (0:ℝ)..Real.pi, (Real.sin x)^4*(1+V x)^3) :=
  sine_integral_kernel_profile_cubic μ c s (Filter.Eventually.of_forall hc) (Filter.Eventually.of_forall hs)
    (continuous_integral_exterior_cosine_kernel μ c s hcm hsm hc hs hint)
    (integrable_sine_exterior_kernel_correction μ c s hcm hsm hc hs hint)

end NLS.ComplexAnalysis
