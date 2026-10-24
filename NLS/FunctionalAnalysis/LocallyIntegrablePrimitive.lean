import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import NLS.FunctionalAnalysis.ComplexAbsoluteContinuity
import Mathlib.Analysis.Calculus.Deriv.Support

/-! # Locally integrable primitives and their compact-test weak equation -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter Function
open scoped ContDiff
namespace NLS.FunctionalAnalysis

private theorem intervalIntegrable_of_locallyIntegrable
    {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : LocallyIntegrable g volume) (a b : ℝ) : IntervalIntegrable g volume a b :=
  intervalIntegrable_iff.mpr
    ((hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

/-- A locally integrable Banach-valued primitive is absolutely continuous
on every finite interval, regardless of the choice of base point. -/
theorem absolutelyContinuousOnInterval_local_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : LocallyIntegrable g volume) (c a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t => ∫ s in c..t, g s) a b := by
  have hi := absolutelyContinuousOnInterval_integral
    (intervalIntegrable_of_locallyIntegrable hg a b) (c := a) (by simp)
  apply absolutelyContinuousOnInterval_congr
    (absolutelyContinuousOnInterval_const_add hi (∫ s in c..a, g s))
  intro t _
  exact intervalIntegral.integral_add_adjacent_intervals
    (intervalIntegrable_of_locallyIntegrable hg c a) (intervalIntegrable_of_locallyIntegrable hg a t)

theorem continuous_local_primitive
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : LocallyIntegrable g volume) (c : ℝ) :
    Continuous (fun t => ∫ s in c..t, g s) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply (absolutelyContinuousOnInterval_local_primitive hg c (t-1) (t+1)).continuousOn.continuousAt
  rw [uIcc_of_le (by linarith : t-1 ≤ t+1)]
  exact Icc_mem_nhds (by linarith) (by linarith)

/-- Integration by parts against every compact smooth real test identifies
the weak derivative of a locally integrable Banach-valued primitive. -/
theorem integral_deriv_smul_local_primitive_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {g : ℝ → E} (hg : LocallyIntegrable g volume) (c : ℝ)
    (ψ : ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ t : ℝ, deriv ψ t • (∫ s in c..t, g s) + ψ t • g t) = 0 := by
  let F : ℝ → E := fun t => ∫ s in c..t, g s
  obtain ⟨C,hC,hbound⟩ := hc.isBounded.exists_pos_norm_lt
  have hz (t : ℝ) (ht : t ∉ tsupport ψ) : ψ t = 0 ∧ deriv ψ t = 0 :=
    ⟨image_eq_zero_of_notMem_tsupport ht,
      image_eq_zero_of_notMem_tsupport (fun h => ht (tsupport_deriv_subset h))⟩
  have hends : ψ (-C) = 0 ∧ ψ C = 0 := by
    constructor
    · apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hb := hbound (-C) ht
      simp only [norm_neg,Real.norm_eq_abs,abs_of_pos hC,lt_self_iff_false] at hb
    · apply image_eq_zero_of_notMem_tsupport
      intro ht
      have hb := hbound C ht
      simp only [Real.norm_eq_abs,abs_of_pos hC,lt_self_iff_false] at hb
  have hsupp : support (fun t => deriv ψ t • F t + ψ t • g t) ⊆ Ioc (-C) C := by
    intro t ht
    have hmem : t ∈ tsupport ψ := by
      by_contra hn
      obtain ⟨h1,h2⟩ := hz t hn
      exact ht (by simp [h1,h2])
    have hb := hbound t hmem
    rw [Real.norm_eq_abs] at hb
    exact ⟨(abs_lt.mp hb).1,(abs_lt.mp hb).2.le⟩
  have hF := absolutelyContinuousOnInterval_local_primitive hg c (-C) C
  have hψa : AbsolutelyContinuousOnInterval ψ (-C) C := (hψ.of_le (by norm_num : (1 : ℕ∞ω) ≤ ∞)).contDiffOn.absolutelyContinuousOnInterval
  have hfa : AbsolutelyContinuousOnInterval (fun t => ψ t • F t) (-C) C := by
    simpa only [Pi.smul_apply] using! hψa.smul hF
  have hi := (((hψ.continuous_deriv (by norm_num)).intervalIntegrable (μ := volume) (-C) C).smul_continuousOn
    hF.continuousOn).add ((intervalIntegrable_of_locallyIntegrable hg (-C) C).continuousOn_smul hψ.continuous.continuousOn)
  have hd : ∀ᵐ t : ℝ, t ∈ uIcc (-C) C → HasDerivAt (fun s => ψ s • F s)
      (deriv ψ t • F t + ψ t • g t) t := by
    filter_upwards [_root_.LocallyIntegrable.ae_hasDerivAt_integral hg] with t ht
    intro _
    simpa only [F,Pi.smul_apply,add_comm] using!
      ((hψ.differentiable (by norm_num)) t).hasDerivAt.smul (ht c)
  have h := integral_eq_sub_of_ac_of_ae_hasDerivAt hfa hi hd
  rw [intervalIntegral.integral_eq_integral_of_support_subset hsupp] at h
  simpa only [hends.1,hends.2,zero_smul,sub_zero] using! h

end NLS.FunctionalAnalysis
