import NLS.Articles.KdVPseudomeasures.SourceLemma29QuarterCutoff
import NLS.KdV.HillWideDiagonalSecondRemainder
import NLS.KdV.HillTwoModeBornCoefficient

/-! A cancelling-weight counterexample to the printed unweighted
potential factor in Lemma 2.9(i), at an actual wide-strip diagonal. -/
noncomputable section
open scoped ENNReal
open NLS.KdV NLS.WeightedCoeff
namespace NLS.Articles.KdVPseudomeasures

theorem norm_lower_of_twoMode_born_error (A B : ℂ) (x : ℝ) (hx : 1024 ≤ x)
    (hB : 1/(64*x) ≤ ‖B‖) (hE : ‖A-B‖ ≤ 8/x^2) :
    1/(128*x) ≤ ‖A‖ := by
  have hx0 : 0<x := by linarith
  have hsmall : 8/x^2 ≤ 1/(128*x) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hx0) (by positivity)).mpr
    nlinarith
  have hnorm : ‖B‖ ≤ ‖A‖+‖A-B‖ := by
    have h := norm_sub_norm_le B A
    rw [norm_sub_rev] at h
    linarith
  have he : 1/(64*x)=2*(1/(128*x)) := by ring
  rw [he] at hB
  linarith

theorem sourceLemma2_9_i_counterexample_at (n : ℕ) (hn : 4096^4 ≤ n) :
    let w := SpectralWeight.sobolev (1/4) (by norm_num)
    let q := twoSymmetricInfinityModes (w.negativeSobolev (1/4)) (2*(n:ℤ)-2)
    let z : ℂ := freeHillValue n
    ∃ (hn2 : 2 ≤ n) (hz : z ∈ wideHillStrip n),
      ‖q‖=1 ∧ q.val 0=0 ∧
      13*endpointHillConstant (1/4)*(n:ℝ)^((1/4:ℝ)-1/2)*‖q‖ ≤ 1/2 ∧
      2*wideEndpointShiftedOperatorNorm w (1/4) (by norm_num) (by norm_num) n hn2 z hz q (-(n:ℤ))*
        ‖endpointForgetWeight w (1/4) q‖ <
          ‖endpointDiagonal (1/4) (by norm_num) (by norm_num) n (endpointForgetWeight w (1/4) q,z)‖ := by
  let w := SpectralWeight.sobolev (1/4) (by norm_num)
  let q := twoSymmetricInfinityModes (w.negativeSobolev (1/4)) (2*(n:ℤ)-2)
  let z : ℂ := freeHillValue n
  have hn3 : 3 ≤ n := by norm_num at hn ⊢; omega
  have hn2 : 2 ≤ n := by omega
  have hnR : (4096:ℝ)^4 ≤ (n:ℝ) := by exact_mod_cast hn
  have hn1024 : (1024:ℝ)≤n := by norm_num at hnR ⊢; linarith
  have hn0 : (0:ℝ)<n := by linarith
  have hm : 2*(n:ℤ)-2 ≠ 0 := by omega
  have hq : ‖q‖=1 := norm_twoModes_cancelling_weight (1/4) (by norm_num) _ hm
  have hq0 : q.val 0=0 := by
    change (twoSymmetricInfinityModes _ _).val 0=0
    rw [twoSymmetricInfinityModes_apply]
    simp only [if_neg (Ne.symm hm),if_neg (show (0:ℤ) ≠ -(2*(n:ℤ)-2) by omega),zero_add]
  have hz : z ∈ wideHillStrip n := by
    change |(freeHillValue n:ℂ).re-freeHillValue n| ≤ 12*(n:ℝ)
    simp only [Complex.ofReal_re,sub_self,abs_zero]
    positivity
  have hv (k : ℤ) : w.negativeSobolev (1/4) k=1 := by
    change (SpectralWeight.sobolev (1/4) (by norm_num)).negativeSobolev (1/4) k=1
    rw [sobolev_negative_weight_cancels]
    rfl
  have hs : 13*endpointHillConstant (1/4)*(n:ℝ)^((1/4:ℝ)-1/2)*‖q‖ ≤ 1/2 := by
    rw [hq]
    norm_num [endpointHillConstant]
    have hroot := quarter_inverse_root_le (n:ℝ) hnR
    norm_num at hroot
    linarith
  have hT : wideEndpointShiftedOperatorNorm w (1/4) (by norm_num) (by norm_num)
      n hn2 z hz q (-(n:ℤ)) ≤ 2/(n:ℝ) := by
    have h := wideEndpointShiftedOperatorNorm_twoModes_unit w (1/4) (by norm_num) (by norm_num)
      hv n hn2 z hz (2*(n:ℤ)-2) (-(n:ℤ)) (1/(n:ℝ)) (by positivity)
        (norm_wideHillSymbol_center_le n (by omega))
    convert h using 1; ring
  have he := wideEndpointDiagonal_second_remainder w (1/4) (by norm_num) (by norm_num)
    hv n hn2 z hz q hs (2/(n:ℝ)) (by positivity) (by apply (div_le_iff₀ hn0).mpr; linarith) hT
  rw [hq0,sub_zero,wideEndpointHillPerturbation_twoModes_modulation_diagonal w (1/4)
    (by norm_num) (by norm_num) n hn2 z hz (2*(n:ℤ)-2) hm] at he
  have hrem :
      ‖endpointDiagonal (1/4) (by norm_num) (by norm_num) n (endpointForgetWeight w (1/4) q,z)-
        (wideHillSymbol n z ((n:ℤ)-(2*(n:ℤ)-2))+wideHillSymbol n z ((n:ℤ)+(2*(n:ℤ)-2)))‖ ≤
          8/(n:ℝ)^2 := by
    convert he using 1; rw [hq]; ring
  have hdiag := norm_lower_of_twoMode_born_error _ _ (n:ℝ) hn1024
    (wideHillSymbol_twoMode_center_sum_lower n hn3) hrem
  refine ⟨hn2,hz,hq,hq0,hs,?_⟩
  have hqsmall : ‖endpointForgetWeight w (1/4) q‖ ≤ 1/4096 :=
    twoModes_quarter_unweighted_norm_le n hn
  have hnonneg : 0 ≤ wideEndpointShiftedOperatorNorm w (1/4) (by norm_num) (by norm_num)
      n hn2 z hz q (-(n:ℤ)) := norm_nonneg _
  have hright : 2*wideEndpointShiftedOperatorNorm w (1/4) (by norm_num) (by norm_num)
      n hn2 z hz q (-(n:ℤ))*‖endpointForgetWeight w (1/4) q‖ ≤ 1/(1024*(n:ℝ)) := by
    calc
      _ ≤ 2*(2/(n:ℝ))*(1/4096) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hqsmall
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  apply lt_of_le_of_lt hright
  apply lt_of_lt_of_le _ hdiag
  exact one_div_lt_one_div_of_lt (by positivity) (by nlinarith : 128*(n:ℝ)<1024*(n:ℝ))

end NLS.Articles.KdVPseudomeasures
