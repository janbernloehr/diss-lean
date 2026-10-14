import NLS.ZakharovShabat.SourceStandardRootGapSideComplex

/-!
# The standard root under the Joukowski map

Outside the unit circle, the normalized standard root has an exact
rational expression. Its derivative quotient is -1/u, including arbitrary
complex gap directions. These identities fix the branch and orientation
for shrinking ellipse contours in Lemma 12.3.
-/

noncomputable section
open Complex
namespace NLS.ZakharovShabat

private theorem sqrt_sq_of_re_pos (z : ℂ) (hz : 0 < z.re) : Complex.sqrt (z^2) = z := by
  have hs : Complex.sqrt (z^2)^2 = z^2 := by
    have h := Complex.cpow_nat_inv_pow (z^2) (Nat.succ_ne_zero 1)
    norm_num at h
    simpa only [Complex.sqrt, one_div] using h
  have hprod : (Complex.sqrt (z^2)-z)*(Complex.sqrt (z^2)+z) = 0 := by
    linear_combination hs
  rcases mul_eq_zero.mp hprod with h | h
  · exact sub_eq_zero.mp h
  · have hr : 0 ≤ (Complex.sqrt (z^2)).re := by
      rw [Complex.sqrt_eq_real_add_ite]
      split_ifs <;> simp <;> positivity
    have hn : Complex.sqrt (z^2) = -z := eq_neg_of_add_eq_zero_left h
    rw [hn, neg_re] at hr
    linarith

private theorem cayley_re (a : ℂ) :
    ((a-1)/(a+1)).re = (‖a‖^2-1)/‖a+1‖^2 := by
  rw [div_re, normSq_eq_norm_sq, ← add_div, sub_re, add_re, sub_im, add_im]
  simp only [one_re, one_im, sub_zero, add_zero]
  rw [← normSq_eq_norm_sq a, normSq_apply]
  congr 1
  ring

private theorem cayley_re_pos (a : ℂ) (ha : 1 < ‖a‖) :
    0 < ((a-1)/(a+1)).re := by
  have hap : a+1 ≠ 0 := by
    intro h
    have he : a = -1 := eq_neg_of_add_eq_zero_left h
    simp [he] at ha
  rw [cayley_re]
  exact div_pos (by nlinarith [norm_nonneg a]) (sq_pos_of_pos (norm_pos_iff.mpr hap))

private theorem root_joukowski (u : ℂ) (hu : 1 < ‖u‖) :
    normalizedStandardRoot 0 4 ((u+u⁻¹)/2) = (u⁻¹-u)/2 := by
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at hu
  have hp : 1 < ‖u^2‖ := by rw [norm_pow]; nlinarith [norm_nonneg u]
  have hd : u^2+1 ≠ 0 := by
    intro h
    have he : u^2 = -1 := eq_neg_of_add_eq_zero_left h
    simp [he] at hp
  have hjmul : ((u+u⁻¹)/2)*(2*u) = u^2+1 := by field_simp [hu0]
  have hj : (u+u⁻¹)/2 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hjmul
    exact hd hjmul.symm
  have hje : (u+u⁻¹)/2 = (u^2+1)/(2*u) := by field_simp [hu0]
  have hr : 1-4/(4*(0-(u+u⁻¹)/2)^2) = ((u^2-1)/(u^2+1))^2 := by
    rw [zero_sub, neg_sq]
    have hc : (4:ℂ)/(4*((u+u⁻¹)/2)^2) = 1/((u+u⁻¹)/2)^2 := by field_simp
    rw [hc, hje, div_pow, one_div, inv_div]
    field_simp [hd]
    ring
  rw [normalizedStandardRoot, hr,
    sqrt_sq_of_re_pos _ (cayley_re_pos (u^2) hp)]
  field_simp [hu0, hd]
  ring

theorem normalizedStandardRoot_joukowski (τ δ u : ℂ) (hδ : δ ≠ 0) (hu : 1 < ‖u‖) :
    normalizedStandardRoot τ ((2*δ)^2) (τ+δ/2*(u+u⁻¹)) =
      δ/2*(u⁻¹-u) := by
  calc
    normalizedStandardRoot τ ((2*δ)^2) (τ+δ/2*(u+u⁻¹)) =
        normalizedStandardRoot τ ((2*δ)^2) (τ+δ*((u+u⁻¹)/2)) := by
      congr 1
      ring
    _ = δ*normalizedStandardRoot 0 4 ((u+u⁻¹)/2) :=
      normalizedStandardRoot_affine_scale τ δ ((u+u⁻¹)/2) hδ
    _ = δ/2*(u⁻¹-u) := by rw [root_joukowski u hu]; ring

theorem normalizedStandardRoot_joukowski_derivative_div (τ δ u : ℂ) (hδ : δ ≠ 0) (hu : 1 < ‖u‖) :
    (δ/2*(1-(u^2)⁻¹)) /
      normalizedStandardRoot τ ((2*δ)^2) (τ+δ/2*(u+u⁻¹)) = -u⁻¹ := by
  have hu0 : u ≠ 0 := by intro h; norm_num [h] at hu
  have hd : u⁻¹-u ≠ 0 := by
    intro h
    have he := congrArg (fun z : ℂ => z*u) (sub_eq_zero.mp h)
    rw [inv_mul_cancel₀ hu0] at he
    have hn := congrArg norm he
    simp only [norm_one, norm_mul] at hn
    nlinarith [norm_nonneg u]
  rw [normalizedStandardRoot_joukowski τ δ u hδ hu]
  apply (div_eq_iff (mul_ne_zero (div_ne_zero hδ (by norm_num)) hd)).mpr
  field_simp [hu0]
  ring

/-- The affine Joukowski map for the gap with midpoint τ and half-gap δ. -/
def standardRootJoukowski (τ δ u : ℂ) : ℂ := τ+δ/2*(u+u⁻¹)

theorem standardRootJoukowski_analyticAt (τ δ u : ℂ) (hu : u ≠ 0) :
    AnalyticAt ℂ (standardRootJoukowski τ δ) u := by
  exact analyticAt_const.add (analyticAt_const.mul
    (analyticAt_id.add (analyticAt_id.inv hu)))

theorem standardRootJoukowski_hasDerivAt (τ δ u : ℂ) (hu : u ≠ 0) :
    HasDerivAt (standardRootJoukowski τ δ) (δ/2*(1-(u^2)⁻¹)) u := by
  change HasDerivAt (fun w : ℂ => τ+δ/2*(w+w⁻¹)) _ u
  simpa only [Pi.add_apply, Pi.inv_apply, id_eq, neg_div, one_div, sub_eq_add_neg] using
    (((hasDerivAt_id u).add ((hasDerivAt_id u).inv hu)).const_mul (δ/2)).const_add τ

end NLS.ZakharovShabat
