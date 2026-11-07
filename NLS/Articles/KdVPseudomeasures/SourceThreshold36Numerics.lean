import NLS.Articles.KdVPseudomeasures.SourceLemma216

/-! Exact consequences of the source adapted-tail threshold (36). -/
noncomputable section
open NLS.KdV
namespace NLS.Articles.KdVPseudomeasures

theorem sourceCoefficientConstant_two_le (r : ℝ) (hr1 : r<1/2) :
    2≤sourceCoefficientConstant r := by
  unfold sourceCoefficientConstant endpointHillConstant
  have hd : 0<1-2*r := by linarith
  have h := div_nonneg (by norm_num : (0:ℝ)≤16) hd.le
  linarith

theorem source_threshold36_bound (r C m : ℝ) (hm : 1≤m) (n : ℕ) (hn : 1≤n)
    (h36 : 8*C/(n:ℝ)^(1/2-r)≤1/(16*m)) :
    C*(n:ℝ)^(r-1/2)*m≤1/128 := by
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have hpow : 0<(n:ℝ)^(1/2-r) := Real.rpow_pos_of_pos hnp _
  have ht := (div_le_div_iff₀ hpow (by linarith : (0:ℝ)<16*m)).mp h36
  have hb : C*m/(n:ℝ)^(1/2-r)≤1/128 := (div_le_iff₀ hpow).mpr (by nlinarith)
  have he : (n:ℝ)^(r-1/2)=((n:ℝ)^(1/2-r))⁻¹ := by
    rw [← Real.rpow_neg hnp.le]
    congr 1
    ring
  calc
    _ = C*m/(n:ℝ)^(1/2-r) := by rw [he]; ring
    _ ≤ _ := hb

theorem source_threshold36_scaled_m (r C m : ℝ) (hr : 0≤r) (hC : 2≤C) (hm : 1≤m)
    (n : ℕ) (hn : 1≤n) (h36 : 8*C/(n:ℝ)^(1/2-r)≤1/(16*m)) :
    (n:ℝ)^r*m≤Real.sqrt (n:ℝ)/256 ∧ m≤Real.sqrt (n:ℝ)/256 := by
  have hb := source_threshold36_bound r C m hm n hn h36
  have hnp : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  have h2 : 2*(n:ℝ)^(r-1/2)*m≤C*(n:ℝ)^(r-1/2)*m :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hnp.le _)) (by linarith)
  have hsmall : (n:ℝ)^(r-1/2)*m≤1/256 := by linarith
  have hp : (n:ℝ)^(r-1/2)*Real.sqrt (n:ℝ)=(n:ℝ)^r := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hnp]
    congr 1
    ring
  have hscaled := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg (n:ℝ))
  have hb' : (n:ℝ)^r*m≤Real.sqrt (n:ℝ)/256 := by
    calc
      _ = ((n:ℝ)^(r-1/2)*m)*Real.sqrt (n:ℝ) := by rw [← hp]; ring
      _ ≤ _ := by simpa only [one_div_mul_eq_div] using hscaled
  refine ⟨hb',?_⟩
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hweight := mul_le_mul_of_nonneg_right (Real.one_le_rpow hnR hr) (by linarith : (0:ℝ)≤m)
  linarith

end NLS.Articles.KdVPseudomeasures
