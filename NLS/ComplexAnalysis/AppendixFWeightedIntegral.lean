import NLS.ComplexAnalysis.ParametricIntervalIntegralAnalytic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Removing the inverse-square-root weight in F.2

The substitution t = s^2 removes the integrable endpoint singularity.
Jointly analytic regular factors therefore give analytic weighted integrals.
-/
noncomputable section
open Set Filter Topology Complex MeasureTheory
open scoped Interval
namespace NLS.ComplexAnalysis

/-- Squaring the interval parameter removes the inverse-square-root endpoint weight. -/
theorem appendixF_inverse_sqrt_substitution (f : ℝ → ℂ) :
    (∫ t in (0:ℝ)..1, f t/(Real.sqrt t:ℂ)) =
      2*(∫ s in (0:ℝ)..1, f (s^2)) := by
  have hder (s : ℝ) : HasDerivAt (fun t : ℝ => t^2) (2*s) s := by
    simpa using! (hasDerivAt_pow 2 s)
  have hsub := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (a := 0) (b := 1) (f := fun s : ℝ => s^2) (f' := fun s => 2*s)
    (g := fun t => f t/(Real.sqrt t:ℂ)) (continuous_pow 2).continuousOn
    (fun s _ => hder s) (by intro s hs; norm_num at hs; exact mul_nonneg (by norm_num) hs.1.le)
  norm_num only [zero_pow,one_pow,Function.comp_apply] at hsub
  rw [← hsub,← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  exact Filter.Eventually.of_forall fun s hs => by
    have hs0 : 0 < s := (by simpa using hs : s ∈ Ioc (0:ℝ) 1).1
    rw [Real.sqrt_sq hs0.le,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
    field_simp [Complex.ofReal_ne_zero.mpr hs0.ne']

/-- A continuous regular factor gives an integrable weighted integrand, including t = 0. -/
theorem appendixF_inverse_sqrt_intervalIntegrable (f : ℝ → ℂ)
    (hf : ContinuousOn f (Icc (0:ℝ) 1)) :
    IntervalIntegrable (fun t => f t/(Real.sqrt t:ℂ)) volume 0 1 := by
  have hder (s : ℝ) : HasDerivAt (fun t : ℝ => t^2) (2*s) s := by
    simpa using! (hasDerivAt_pow 2 s)
  have hiff := intervalIntegral.integrable_deriv_smul_comp_iff_of_deriv_nonneg
    (a := 0) (b := 1) (f := fun s : ℝ => s^2) (f' := fun s => 2*s)
    (g := fun t => f t/(Real.sqrt t:ℂ)) (continuous_pow 2).continuousOn
    (fun s _ => hder s) (by intro s hs; norm_num at hs; exact mul_nonneg (by norm_num) hs.1.le)
  norm_num only [zero_pow,one_pow,Function.comp_apply] at hiff
  apply hiff.mp
  have hcont : ContinuousOn (fun s : ℝ => (2:ℂ)*f (s^2)) (Icc (0:ℝ) 1) := by
    apply continuousOn_const.mul (hf.comp (continuous_pow 2).continuousOn ?_)
    intro s hs
    exact ⟨sq_nonneg s,by nlinarith [hs.1,hs.2]⟩
  apply (hcont.intervalIntegrable_of_Icc (by norm_num)).congr_ae
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
  have hs0 : 0 < s := (by simpa using hs : s ∈ Ioc (0:ℝ) 1).1
  rw [Real.sqrt_sq hs0.le,Complex.real_smul,Complex.ofReal_mul,Complex.ofReal_ofNat]
  field_simp [Complex.ofReal_ne_zero.mpr hs0.ne']

/-- The inverse-square-root weighted integral of a joint analytic family is analytic
in arbitrary Banach parameters on the same open parameter domain. -/
theorem appendixF_inverse_sqrt_integral_analytic
    {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (F : ℂ × X → ℂ) (D : Set (ℂ × X)) (hD : IsOpen D)
    (hF : AnalyticOnNhd ℂ F D) (V : Set X) (hV : IsOpen V)
    (hsegment : ∀ x ∈ V, ∀ t ∈ Icc (0:ℝ) 1, ((t:ℂ),x) ∈ D) :
    AnalyticOnNhd ℂ (fun x => ∫ t in (0:ℝ)..1, F ((t:ℂ),x)/(Real.sqrt t:ℂ)) V := by
  let T : ℂ × X → ℂ × X := fun p => (p.1^2,p.2)
  have hT : AnalyticOnNhd ℂ T univ := fun _ _ =>
    (analyticAt_fst.pow 2).prod analyticAt_snd
  have hG : AnalyticOnNhd ℂ (F ∘ T) (T ⁻¹' D) := fun p hp =>
    (hF (T p) hp).comp (hT p (mem_univ p))
  have hTc : Continuous T := (continuous_fst.pow 2).prodMk continuous_snd
  have hseg : ∀ x ∈ V, ∀ t ∈ uIcc (0:ℝ) 1, ((t:ℂ),x) ∈ T ⁻¹' D := by
    intro x hx t ht
    have ht' : t ∈ Icc (0:ℝ) 1 := by simpa using ht
    have hs : t^2 ∈ Icc (0:ℝ) 1 := ⟨sq_nonneg t,by nlinarith [ht'.1,ht'.2]⟩
    simpa only [mem_preimage,T,← Complex.ofReal_pow] using hsegment x hx (t^2) hs
  have hI := analyticOnNhd_intervalIntegral_of_jointAnalytic (F ∘ T)
    (hD.preimage hTc) hG 0 1 hV hseg
  have heq (x : X) : (∫ t in (0:ℝ)..1, F ((t:ℂ),x)/(Real.sqrt t:ℂ)) =
      2*(∫ t in (0:ℝ)..1, (F ∘ T) ((t:ℂ),x)) := by
    simpa only [T,Function.comp_apply,Complex.ofReal_pow] using
      appendixF_inverse_sqrt_substitution (fun t => F ((t:ℂ),x))
  intro x hx
  apply (analyticAt_const.mul (hI x hx)).congr
  exact Filter.Eventually.of_forall fun y => (heq y).symm

end NLS.ComplexAnalysis
