import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal

namespace NLS.ComplexAnalysis

theorem eq_of_zero_of_pos_derivative_at_zeros
    (f f' : ℝ → ℝ) (a b : ℝ) (hab : a≤b)
    (hd : ∀ t∈Icc a b, HasDerivAt f (f' t) t)
    (hpos : ∀ t∈Icc a b, f t=0 → 0<f' t)
    (ha : f a=0) (hb : f b=0) : a=b := by
  by_contra hne
  have hab' : a<b := lt_of_le_of_ne hab hne
  have hn : ∀ ⦃t⦄, t∈Icc a b → -f t≤0 :=
    image_le_of_deriv_right_lt_deriv_boundary
      (fun t ht => (hd t ht).continuousAt.neg.continuousWithinAt)
      (fun t ht => (hd t (Ico_subset_Icc_self ht)).neg.hasDerivWithinAt)
      (by simp [ha]) (fun t => hasDerivAt_const t (0 : ℝ))
      (by
        intro t ht hz
        have hzero : f t=0 := neg_eq_zero.mp hz
        exact neg_neg_of_pos (hpos t (Ico_subset_Icc_self ht) hzero))
  have hs : ∀ᶠ t in 𝓝[<] b, 0<slope f b t :=
    ((hd b ⟨hab,le_rfl⟩).tendsto_slope.mono_left (nhdsLT_le_nhdsNE b))
      (Ioi_mem_nhds (hpos b ⟨hab,le_rfl⟩ hb))
  obtain ⟨t,ht,hst⟩ := (Filter.Eventually.and (Ioo_mem_nhdsLT hab') hs).exists
  have hft : 0≤f t := neg_nonpos.mp (hn ⟨ht.1.le,ht.2.le⟩)
  rw [slope_def_field,hb,sub_zero] at hst
  have hnon : f t/(t-b)≤0 := div_nonpos_of_nonneg_of_nonpos hft (sub_nonpos.mpr ht.2.le)
  exact (not_lt_of_ge hnon) hst

end NLS.ComplexAnalysis
