import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ComplexConjugate ENNReal

namespace NLS.ComplexAnalysis

theorem tendsto_sq_punctured (z : ℂ) : Tendsto (fun w : ℂ => w^2) (𝓝[≠] z) (𝓝[≠] (z^2)) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨(continuous_id.pow 2).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,?_⟩
  by_cases hz : z=0
  · subst z
    filter_upwards [self_mem_nhdsWithin] with w hw
    simp only [mem_compl_iff,mem_singleton_iff] at hw ⊢
    simpa only [zero_pow (by norm_num : 2≠0)] using pow_ne_zero 2 hw
  · have hn : z≠-z := by
      intro he
      apply hz
      linear_combination he/2
    have hne : ∀ᶠ w in 𝓝 z, w≠-z := eventually_ne_nhds hn
    filter_upwards [self_mem_nhdsWithin,hne.filter_mono nhdsWithin_le_nhds] with w hw hwn
    simp only [mem_compl_iff,mem_singleton_iff] at hw ⊢
    intro he
    rcases eq_or_eq_neg_of_sq_eq_sq w z he with h | h
    · exact hw h
    · exact hwn h

end NLS.ComplexAnalysis
