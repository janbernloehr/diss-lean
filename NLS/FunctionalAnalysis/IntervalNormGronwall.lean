import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.Calculus.Deriv.Comp

/-! # Two-sided norm growth on a closed interval

Within-interval derivatives suffice at both endpoints. The estimate uses
elapsed absolute time and therefore applies in either time direction.
-/
noncomputable section
open Set Filter Topology
namespace NLS.FunctionalAnalysis
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Forward norm growth, using only derivatives on the closed interval. -/
theorem norm_le_exp_of_hasDerivWithinAt_Icc
    {f f' : ℝ → E} {a b K : ℝ}
    (hd : ∀ r ∈ Icc a b, HasDerivWithinAt f (f' r) (Icc a b) r)
    (hb : ∀ r ∈ Icc a b, ‖f' r‖ ≤ K*‖f r‖) (hab : a ≤ b) :
    ‖f b‖ ≤ ‖f a‖*Real.exp (K*(b-a)) := by
  have hr (r : ℝ) (h : r ∈ Ico a b) : HasDerivWithinAt f (f' r) (Ici r) r := by
    apply (hd r ⟨h.1,h.2.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds h.2)] with x hx hxb
    exact ⟨h.1.trans hx,hxb.le⟩
  have hg := norm_le_gronwallBound_of_norm_deriv_right_le
    (fun r h => (hd r h).continuousWithinAt) hr (le_refl ‖f a‖) (ε := 0)
    (fun r h => by simpa only [add_zero] using hb r ⟨h.1,h.2.le⟩) b ⟨hab,le_rfl⟩
  simpa only [gronwallBound_ε0] using hg

/-- Two-sided exponential growth between any two endpoints, including equal endpoints. -/
theorem norm_le_exp_abs_of_hasDerivWithinAt_Icc
    {f f' : ℝ → E} {a b K : ℝ}
    (hd : ∀ r ∈ Icc (min a b) (max a b),
      HasDerivWithinAt f (f' r) (Icc (min a b) (max a b)) r)
    (hb : ∀ r ∈ Icc (min a b) (max a b), ‖f' r‖ ≤ K*‖f r‖) :
    ‖f b‖ ≤ ‖f a‖*Real.exp (K*|b-a|) := by
  by_cases hab : a ≤ b
  · have h := norm_le_exp_of_hasDerivWithinAt_Icc
      (by simpa only [min_eq_left hab,max_eq_right hab] using hd)
      (by simpa only [min_eq_left hab,max_eq_right hab] using hb) hab
    simpa only [abs_of_nonneg (sub_nonneg.mpr hab)] using h
  · have hba := le_of_not_ge hab
    have hm : MapsTo (fun r : ℝ => -r) (Icc (-a) (-b)) (Icc (min a b) (max a b)) := by
      intro r hr
      simp only [min_eq_right hba,max_eq_left hba,mem_Icc]
      constructor <;> linarith [hr.1,hr.2]
    have hneg (r : ℝ) (hr : r ∈ Icc (-a) (-b)) :
        HasDerivWithinAt (fun t => f (-t)) (-f' (-r)) (Icc (-a) (-b)) r := by
      simpa only [Function.comp_def,neg_one_smul] using
        (hd (-r) (hm hr)).scomp r (hasDerivAt_neg r).hasDerivWithinAt hm
    have h := norm_le_exp_of_hasDerivWithinAt_Icc hneg
      (fun r hr => by simpa only [norm_neg] using hb (-r) (hm hr)) (by linarith : -a ≤ -b)
    have ht : -b - -a = |b-a| := by rw [abs_of_nonpos (sub_nonpos.mpr hba)]; ring
    simpa only [neg_neg,ht] using h

end NLS.FunctionalAnalysis
