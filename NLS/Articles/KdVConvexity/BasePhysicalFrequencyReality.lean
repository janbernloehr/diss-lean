import NLS.Articles.KdVConvexity.BasePhysicalFrequencyConstruction
import NLS.Articles.KdVConvexity.NativeOriginalFrequencyCompatibility

/-! # Reality of the actual physical base frequencies on the whole positive cone -/
noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.Articles.KdVConvexity

/-- Preparation for Theorem 1.3: the actual base physical frequencies
are real on the whole original nonnegative weighted base action cone. -/
theorem BasePhysicalFrequencyExtension.frequency_real_on_cone
    (B : BasePhysicalFrequencyExtension) (a : BaseActionSpace)
    (ha : a∈WeightedCoeff.nonnegativeLocus baseActionWeight 1) (n : ℕ+) :
    (B.frequency n a).im=0 := by
  classical
  obtain ⟨D⟩ := NLS.Articles.KdVKdV2Frequencies.nonempty_globalRoughAbelianForwardData
  let b (S : Finset ℤ) : OriginalActionSpace :=
    ⟨fun j => if j∈S then a.val j else 0,by
      apply memℓp_gen
      apply summable_of_ne_finset_zero (s := S)
      intro j hj
      simp only [if_neg hj,mul_zero,norm_zero,ENNReal.toReal_one,Real.rpow_one]⟩
  have hb (S : Finset ℤ) : b S∈WeightedCoeff.nonnegativeLocus originalActionWeight 1 := by
    intro j
    change (if j∈S then a.val j else 0).im=0 ∧ 0≤(if j∈S then a.val j else 0).re
    by_cases hj : j∈S
    · simpa only [if_pos hj] using ha j
    · simp only [if_neg hj,zero_im,zero_re,le_refl,and_self]
  have hinc (S : Finset ℤ) : baseActionInclusion (originalActionInclusion (b S))=
      WeightedCoeff.truncate baseActionWeight 1 S a := by
    apply Subtype.ext
    funext j
    simp only [baseActionInclusion_apply,originalActionInclusion_apply,
      Equiv.symm_apply_apply,WeightedCoeff.truncate_apply]
    rfl
  have hz (S : Finset ℤ) :
      (B.frequency n (WeightedCoeff.truncate baseActionWeight 1 S a)).im=0 := by
    rw [←hinc S,B.physical_agreement ⟨b S,hb S⟩ n,
      originalPhysicalFrequency_eq_nativeOriginalFrequency D ⟨b S,hb S⟩ n]
    rfl
  have ht := (Complex.continuous_im.continuousAt.comp
    (B.analytic n a (B.contains_cone ha)).continuousAt).tendsto.comp
      (WeightedCoeff.tendsto_truncate baseActionWeight 1 (by simp : (1 : ℝ≥0∞)≠⊤) a)
  have hzero : Tendsto (fun S : Finset ℤ =>
      (B.frequency n (WeightedCoeff.truncate baseActionWeight 1 S a)).im) atTop (𝓝 0) := by
    simpa only [hz] using (tendsto_const_nhds : Tendsto (fun _ : Finset ℤ => (0 : ℝ)) atTop (𝓝 0))
  exact tendsto_nhds_unique ht hzero

end NLS.Articles.KdVConvexity
