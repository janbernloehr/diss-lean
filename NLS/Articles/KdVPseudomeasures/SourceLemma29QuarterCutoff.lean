import NLS.Articles.KdVPseudomeasures.SourceLemma29CancelledNorms

/-! Explicit fourth-root bounds for the cancelling-weight diagnostic at
s=-1/4. These estimates concern the source's actual potential norms. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem quarter_root_ge_4096 (x : ℝ) (hx : (4096:ℝ)^4 ≤ x) :
    4096 ≤ x^(1/4:ℝ) := by
  have h := Real.rpow_le_rpow (by positivity : (0:ℝ)≤4096^4) hx (by norm_num : (0:ℝ)≤1/4)
  have he : ((4096:ℝ)^4)^(1/4:ℝ) = 4096 := by
    convert Real.pow_rpow_inv_natCast (x := (4096:ℝ)) (by norm_num) (by norm_num : (4:ℕ)≠0) using 1; norm_num
  rwa [he] at h

theorem quarter_inverse_root_le (x : ℝ) (hx : (4096:ℝ)^4 ≤ x) :
    x^(-(1/4:ℝ)) ≤ 1/4096 := by
  have hx0 : 0 ≤ x := (by positivity : (0:ℝ)≤4096^4).trans hx
  rw [Real.rpow_neg hx0]
  exact (inv_anti₀ (by norm_num : (0:ℝ)<4096) (quarter_root_ge_4096 x hx)).trans_eq (by norm_num)

theorem twoModes_quarter_unweighted_norm_le (n : ℕ) (hn : 4096^4 ≤ n) :
    ‖endpointForgetWeight (SpectralWeight.sobolev (1/4) (by norm_num)) (1/4)
      (twoSymmetricInfinityModes
        ((SpectralWeight.sobolev (1/4) (by norm_num)).negativeSobolev (1/4)) (2*(n:ℤ)-2))‖ ≤
          1/4096 := by
  have hn3 : 3 ≤ n := by norm_num at hn ⊢; omega
  have hm : 2*(n:ℤ)-2 ≠ 0 := by omega
  rw [norm_twoModes_unweighted_negative (1/4) (by norm_num) _ hm,Weight.sobolev_apply]
  have hbase : (4096:ℝ)^4 ≤ 1+|((2*(n:ℤ)-2:ℤ):ℝ)| := by
    have hnR : (4096:ℝ)^4 ≤ (n:ℝ) := by exact_mod_cast hn
    have hnR3 : (3:ℝ)≤n := by exact_mod_cast hn3
    push_cast
    rw [abs_of_nonneg (by linarith)]
    linarith
  simpa only [one_div] using (inv_anti₀ (by norm_num : (0:ℝ)<4096) (quarter_root_ge_4096 _ hbase))

end NLS.Articles.KdVPseudomeasures
