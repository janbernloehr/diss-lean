import NLS.Articles.KdVPseudomeasures.SourceWideSharpCouplings
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Complex.ExponentialBounds

/-! Numerical inequalities with the literal constants in (35) and
Lemma 2.16, including the logarithmic endpoint. -/
noncomputable section
open Set
namespace NLS.Articles.KdVPseudomeasures

theorem source_log_one_add_le_sqrt (x : ℝ) (hx : 1≤x) :
    Real.log (1+x)≤Real.sqrt x := by
  let f := fun t : ℝ => Real.sqrt t-Real.log (1+t)
  have hd (t : ℝ) (ht : 1≤t) : HasDerivAt f (1/(2*Real.sqrt t)-1/(1+t)) t := by
    have hp : 0<t := by linarith
    exact (Real.hasDerivAt_sqrt hp.ne').sub
      (((hasDerivAt_id t).const_add 1).log (by change 1+t≠0; linarith))
  have hm : MonotoneOn f (Ici 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht1 : 1≤t := interior_subset ht
    have hp : 0<t := by linarith
    have hs : 0<Real.sqrt t := Real.sqrt_pos.mpr hp
    have hsq := Real.sq_sqrt hp.le
    apply sub_nonneg.mpr
    apply (div_le_div_iff₀ (by linarith : 0<1+t) (by positivity : 0<2*Real.sqrt t)).mpr
    nlinarith [sq_nonneg (Real.sqrt t-1)]
  have hf := hm (by simp) hx hx
  have hlog := Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)
  simp only [f,Real.sqrt_one,show (1:ℝ)+1=2 by norm_num] at hf
  linarith

theorem source_epsilon_log_bound (r : ℝ) (n : ℕ) (hn : 2≤n) :
    sourcePredualEpsilon r n≤Real.log (1+(n:ℝ))/(n:ℝ)^(1-r) := by
  have hnR : (2:ℝ)≤n := by exact_mod_cast hn
  have hlog : 1≤Real.log (1+(n:ℝ)) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ)<3) (by linarith : (3:ℝ)≤1+n)
    linarith [Real.log_three_gt_d9]
  unfold sourcePredualEpsilon
  split_ifs with hr
  · subst r
    simp
  · exact div_le_div_of_nonneg_right hlog (Real.rpow_nonneg (by positivity) _)

theorem source_threshold35_bound (r C m : ℝ) (n : ℕ) (hn : 1≤n)
    (h : 16*C*m/(n:ℝ)^(1/2-r)≤1/2) :
    C*(n:ℝ)^(r-1/2)*m≤1/32 := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have he : (n:ℝ)^(r-1/2)=((n:ℝ)^(1/2-r))⁻¹ := by
    rw [← Real.rpow_neg hnR.le]
    congr 1
    ring
  rw [he]
  rw [div_eq_mul_inv] at h
  nlinarith

theorem source_log_power_le_half (r : ℝ) (n : ℕ) (hn : 1≤n) :
    Real.log (1+(n:ℝ))/(n:ℝ)^(1-r)≤(n:ℝ)^(r-1/2) := by
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  calc
    _ ≤ Real.sqrt (n:ℝ)/(n:ℝ)^(1-r) :=
      div_le_div_of_nonneg_right (source_log_one_add_le_sqrt n (by exact_mod_cast hn))
        (Real.rpow_nonneg hnR.le _)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,div_eq_mul_inv,← Real.rpow_neg hnR.le,← Real.rpow_add hnR]
      congr 1
      ring

end NLS.Articles.KdVPseudomeasures
