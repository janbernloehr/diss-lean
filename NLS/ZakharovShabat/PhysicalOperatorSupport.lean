import NLS.ZakharovShabat.L2WholeLineTestOperator

/-! # Support of the original physical differential expression -/
noncomputable section
set_option autoImplicit false
open Set Function
namespace NLS.ZakharovShabat

/-- The original differential expression vanishes off the topological
support of its input, without any regularity condition on the potential. -/
theorem physicalOperator_eq_zero_of_notMem_tsupport (φ f : ℝ → ℂ × ℂ)
    {t : ℝ} (ht : t ∉ tsupport f) : physicalOperator φ f t = 0 := by
  have hd : HasDerivAt f 0 t := HasDerivAt.of_notMem_tsupport ht
  have hz : f t = 0 := image_eq_zero_of_notMem_tsupport ht
  simp only [physicalOperator,(HasFDerivAt.hasDerivAt hd.fst).deriv,
    (HasFDerivAt.hasDerivAt hd.snd).deriv,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,one_smul,hz]
  simp

/-- Compact support is preserved by the actual physical expression. -/
theorem hasCompactSupport_physicalOperator (φ f : ℝ → ℂ × ℂ)
    (hf : HasCompactSupport f) : HasCompactSupport (physicalOperator φ f) := by
  apply hf.mono'
  intro t ht
  by_contra hn
  exact ht (physicalOperator_eq_zero_of_notMem_tsupport φ f hn)

end NLS.ZakharovShabat
