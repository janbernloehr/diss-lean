import NLS.Articles.KdVPseudomeasures.SourceThreshold36Numerics
import NLS.KdV.PseudomeasureWideAnalyticCoefficients
import NLS.KdV.PseudomeasureDiagonalRoot

/-! The physical coefficients and diagonal root have the small full-strip
bounds needed for the genuinely complex Lemma 2.20, under exactly (36). -/
noncomputable section
open NLS.KdV
open scoped ENNReal
namespace NLS.Articles.KdVPseudomeasures

theorem source_threshold36_small (r C m : ℝ) (hr1 : r<1/2)
    (hC : sourceCoefficientConstant r≤C) (hm : 1≤m) (n : ℕ) (hn : 1≤n)
    (h36 : 8*C/(n:ℝ)^(1/2-r)≤1/(16*m)) (Q : ℝ) (hQ0 : 0≤Q) (hQ : Q≤m) :
    sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*Q≤1/128 := by
  have hcpos : 0≤C := by linarith [sourceCoefficientConstant_two_le r hr1]
  calc
    _ ≤ C*(n:ℝ)^(r-1/2)*Q :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (by positivity)) hQ0
    _ ≤ C*(n:ℝ)^(r-1/2)*m := mul_le_mul_of_nonneg_left hQ (by positivity)
    _ ≤ _ := source_threshold36_bound r C m hm n hn h36

variable (r : ℝ) (hr : 0≤r) (hr1 : r<1/2) (C m : ℝ)
variable (hC : sourceCoefficientConstant r≤C) (hm : 1≤m)
variable (n : ℕ) (hn : 2≤n) (h36 : 8*C/(n:ℝ)^(1/2-r)≤1/(16*m))
variable (q : WeightedCoeff (SpectralWeight.one.negativeSobolev r) ⊤) (hq : ‖q‖≤m) (hq0 : q.val 0=0)

include hr1 hC hm hn h36 hq in
theorem source_threshold36_wide_small :
    13*endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤1/2 :=
  (source_threshold36_small r C m hr1 hC hm n (by omega) h36 ‖q‖ (norm_nonneg q) hq).trans (by norm_num)

include hr1 hC hm hn h36 hq hq0 in
theorem source_threshold36_diagonal_bound (z : ℂ) (hz : z ∈ wideHillStrip n) :
    ‖endpointDiagonal r hr hr1 n (q,z)‖≤m/64 := by
  have hs := source_threshold36_wide_small r hr1 C m hC hm n hn h36 q hq
  have hd := source_wideDiagonal_error r hr hr1 n hn z hz q hs
  rw [hq0,sub_zero] at hd
  have hsmall := source_threshold36_small r C m hr1 hC hm n (by omega) h36 ‖q‖ (norm_nonneg q) hq
  have hprod := mul_le_mul_of_nonneg_right hsmall (norm_nonneg q)
  nlinarith

include hr1 hC hm hn h36 hq in
theorem source_threshold36_coupling_bounds (z : ℂ) (hz : z ∈ wideHillStrip n) :
    ‖endpointUpperCoupling r hr hr1 n (q,z)‖≤Real.sqrt (n:ℝ)/32 ∧
    ‖endpointLowerCoupling r hr hr1 n (q,z)‖≤Real.sqrt (n:ℝ)/32 := by
  have hs := source_threshold36_wide_small r hr1 C m hC hm n hn h36 q hq
  have h₁ := (wideEndpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs).1
  have h₂ := (wideEndpointHillEffectiveCorrection_columns_le r hr hr1 n hn z hz q hs).2
  have hup : ‖endpointUpperCoupling r hr hr1 n (q,z)‖≤2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
    unfold endpointUpperCoupling
    rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (q,z) hz hs]
    exact (norm_fst_le _).trans h₂
  have hlo : ‖endpointLowerCoupling r hr hr1 n (q,z)‖≤2*Weight.sobolev r (2*(n:ℤ))*‖q‖ := by
    unfold endpointLowerCoupling
    rw [endpointEffectiveFamily_eq_wide r hr hr1 n hn (q,z) hz hs]
    exact (norm_snd_le _).trans h₁
  have hweight := sobolev_two_mode_le r hr hr1 n (by omega)
  have hscaled := (source_threshold36_scaled_m r C m hr
    ((sourceCoefficientConstant_two_le r hr1).trans hC) hm n (by omega) h36).1
  have hqprod := mul_le_mul_of_nonneg_left hq ((Weight.sobolev r).positive (2*(n:ℤ))).le
  have hprod := mul_le_mul_of_nonneg_right hweight (by linarith : (0:ℝ)≤m)
  have hsqrt0 := Real.sqrt_nonneg (n:ℝ)
  constructor <;> nlinarith

include hr1 hC hm hn h36 hq hq0 in
theorem source_threshold36_root_bound :
    ‖endpointHillDiagonalRoot r hr hr1 n (by omega) q-(freeHillValue n:ℂ)‖≤m/64 := by
  have hs := endpointHill_small_of_wide_small r hr1 n q
    (source_threshold36_wide_small r hr1 C m hC hm n hn h36 q hq)
  have hd := endpointHillDiagonalRoot_error_le r hr hr1 n (by omega) q hs
  rw [hq0,sub_zero] at hd
  have hcbase : endpointHillConstant r≤sourceCoefficientConstant r := by
    unfold sourceCoefficientConstant
    linarith [endpointHillConstant_pos r hr1]
  have hbase : endpointHillConstant r*(n:ℝ)^(r-1/2)*‖q‖≤sourceCoefficientConstant r*(n:ℝ)^(r-1/2)*‖q‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcbase
      (Real.rpow_nonneg (show (0:ℝ)≤n by positivity) (r-1/2))) (norm_nonneg q)
  have hsmall := (hbase.trans (source_threshold36_small r C m hr1 hC hm n (by omega) h36 ‖q‖ (norm_nonneg q) hq))
  have hprod := mul_le_mul_of_nonneg_right hsmall (norm_nonneg q)
  nlinarith

end NLS.Articles.KdVPseudomeasures
