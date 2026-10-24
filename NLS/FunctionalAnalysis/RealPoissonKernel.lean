import NLS.FunctionalAnalysis.RealResolventKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # The Poisson kernel obtained from the original resolvent -/
noncomputable section
set_option autoImplicit false
open MeasureTheory Complex Set
namespace NLS.FunctionalAnalysis

/-- The unnormalized real Poisson kernel, with no factor of pi. -/
def realPoissonKernel (x ε t : ℝ) : ℝ := ε / ((x-t)^2+ε^2)

/-- The sign agrees with the original pencil z-T. -/
theorem realPoissonKernel_eq_neg_im (x ε t : ℝ) :
    realPoissonKernel x ε t = -(((x : ℂ)+(ε : ℂ)*I-(t : ℂ))⁻¹).im := by
  simp [realPoissonKernel,Complex.inv_im,Complex.normSq_apply,pow_two,neg_div]

theorem realPoissonKernel_nonneg (x ε t : ℝ) (hε : 0 ≤ ε) :
    0 ≤ realPoissonKernel x ε t :=
  div_nonneg hε (add_nonneg (sq_nonneg _) (sq_nonneg _))

/-- A centered interval has a uniform lower bound for this kernel. -/
theorem realPoissonKernel_lower_bound (x ε t : ℝ) (hε : 0 < ε)
    (ht : |x-t| ≤ ε) : 1/(2*ε) ≤ realPoissonKernel x ε t := by
  have hd : 0 < (x-t)^2+ε^2 := add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos hε)
  have hs : (x-t)^2 ≤ ε^2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hε.le).mpr ht
  apply (div_le_div_iff₀ (by positivity) hd).mpr
  nlinarith

/-- Every finite real measure integrates the Poisson kernel at positive height. -/
theorem integrable_realPoissonKernel (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x ε : ℝ) (hε : 0 < ε) : Integrable (realPoissonKernel x ε) μ := by
  have hz : ((x : ℂ)+(ε : ℂ)*I).im ≠ 0 := by simpa using ne_of_gt hε
  have hf := (Complex.imCLM.integrable_comp
    (integrable_realResolventKernel μ ((x : ℂ)+(ε : ℂ)*I) hz)).neg
  have he : realPoissonKernel x ε = (fun t : ℝ => -(((x : ℂ)+(ε : ℂ)*I-(t : ℂ))⁻¹).im) :=
    funext (realPoissonKernel_eq_neg_im x ε)
  rw [he]
  exact hf

/-- The Poisson integral is the negative imaginary part of the Cauchy integral. -/
theorem integral_realPoissonKernel_eq_neg_im (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x ε : ℝ) (hε : 0 < ε) :
    ∫ t, realPoissonKernel x ε t ∂μ =
      -(∫ t, ((x : ℂ)+(ε : ℂ)*I-(t : ℂ))⁻¹ ∂μ).im := by
  have hz : ((x : ℂ)+(ε : ℂ)*I).im ≠ 0 := by simpa using ne_of_gt hε
  simp_rw [realPoissonKernel_eq_neg_im]
  have hi : (∫ t, (((x : ℂ)+(ε : ℂ)*I-(t : ℂ))⁻¹).im ∂μ) =
      (∫ t, ((x : ℂ)+(ε : ℂ)*I-(t : ℂ))⁻¹ ∂μ).im :=
    integral_im (integrable_realResolventKernel μ _ hz)
  rw [integral_neg,hi]

/-- A positive-height Poisson integral controls the mass of its centered interval. -/
theorem measureReal_Icc_le_poisson_integral (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x ε : ℝ) (hε : 0 < ε) :
    μ.real (Icc (x-ε) (x+ε)) ≤ 2*ε*(∫ t, realPoissonKernel x ε t ∂μ) := by
  have hi := integrable_realPoissonKernel μ x ε hε
  have hlocal : μ.real (Icc (x-ε) (x+ε)) * (1/(2*ε)) ≤
      ∫ t in Icc (x-ε) (x+ε), realPoissonKernel x ε t ∂μ := by
    have h := setIntegral_mono_on
      (integrable_const (1/(2*ε) : ℝ)).integrableOn hi.integrableOn
      measurableSet_Icc (fun t (ht : t ∈ Icc (x-ε) (x+ε)) =>
        realPoissonKernel_lower_bound x ε t hε (abs_le.mpr ⟨by linarith [ht.2],by linarith [ht.1]⟩))
    simpa only [setIntegral_const,smul_eq_mul] using h
  have hglobal := hlocal.trans (setIntegral_le_integral hi
    (Filter.Eventually.of_forall (fun t => realPoissonKernel_nonneg x ε t hε.le)))
  have hm : 0 < 2*ε := by positivity
  have he : μ.real (Icc (x-ε) (x+ε)) / (2*ε) ≤ ∫ t, realPoissonKernel x ε t ∂μ := by
    simpa only [one_div,div_eq_mul_inv,one_mul] using hglobal
  exact (div_le_iff₀ hm).mp he |>.trans_eq (mul_comm _ _)

/-- A uniform Poisson bound gives the corresponding interval mass bound. -/
theorem measureReal_Icc_le_of_poisson_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    (x ε C : ℝ) (hε : 0 < ε) (hC : (∫ t, realPoissonKernel x ε t ∂μ) ≤ C) :
    μ.real (Icc (x-ε) (x+ε)) ≤ 2*ε*C :=
  (measureReal_Icc_le_poisson_integral μ x ε hε).trans
    (mul_le_mul_of_nonneg_left hC (by positivity))

end NLS.FunctionalAnalysis
