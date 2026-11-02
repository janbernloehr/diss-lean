import NLS.ComplexAnalysis.ContinuousLogarithmUnique
import Mathlib.Analysis.Complex.AbsMax

/-! # Strict positivity of a nonconstant holomorphic real part -/

noncomputable section
open Set Metric Complex Filter Topology
namespace NLS.ComplexAnalysis

/-- The maximum modulus principle upgrades a nonnegative holomorphic
real part to a strictly positive one, unless the function is constant. -/
theorem re_pos_of_analyticOnNhd_nonneg_not_constant
    (f : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U) (hc : IsPreconnected U)
    (hf : AnalyticOnNhd ℂ f U) (hnonneg : ∀ z ∈ U, 0 ≤ (f z).re)
    (hnot : ¬ ∃ c : ℂ, ∀ z ∈ U, f z = c) :
    ∀ z ∈ U, 0 < (f z).re := by
  intro z hz
  by_contra hpos
  have hzero : (f z).re = 0 := le_antisymm (not_lt.mp hpos) (hnonneg z hz)
  let G : ℂ → ℂ := fun w => exp (-f w)
  have hG : AnalyticOnNhd ℂ G U := fun w hw => (hf w hw).neg.cexp
  have hnorm : ‖G z‖ = 1 := by simp only [G, norm_exp, neg_re, hzero, neg_zero, Real.exp_zero]
  have hmax : IsMaxOn (norm ∘ G) U z := by
    intro w hw
    change ‖G w‖ ≤ ‖G z‖
    rw [hnorm]
    simp only [G, norm_exp, neg_re, Real.exp_le_one_iff, neg_nonpos]
    exact hnonneg w hw
  have he := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm hc hU hG.differentiableOn hz hmax
  have heq := continuousLogarithms_eqOn (fun w => -f w) (fun _ => -f z) U hc
    hf.continuousOn.neg continuousOn_const (fun w hw => he hw) z hz rfl
  exact hnot ⟨f z, fun w hw => neg_injective (heq hw)⟩

end NLS.ComplexAnalysis
