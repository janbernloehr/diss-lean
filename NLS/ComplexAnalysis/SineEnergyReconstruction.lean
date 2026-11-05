import NLS.ComplexAnalysis.CosineNormEstimates

/-! # Recovering a quadratic energy from the small sine residual

The Fourier Dirichlet equation is expressed in frequency. This estimate
controls its quadratic energy error by the same inverse-index remainder.
-/
noncomputable section
open Complex
namespace NLS.ComplexAnalysis

theorem norm_quadratic_energy_error_of_sine_residual (z c m v : ℂ) (k t e : ℝ)
    (hk : 1 ≤ k) (ht1 : t ≤ 1) (he : 1 ≤ e)
    (hz : ‖z‖ ≤ 5*k) (hm : ‖m‖ ≤ t)
    (hδ1 : ‖z-c‖ ≤ 1) (hδ : ‖z-c‖ ≤ 8*e^2*t/k)
    (hres : ‖2*z*sin (z-c)+v-cos (z-c)*m‖ ≤ 32*e^3*t^2/k) :
    ‖z^2-c^2-m+v‖ ≤ 1024*e^4*t^2/k := by
  let δ := z-c
  let R := 2*z*sin δ+v-cos δ*m
  have hs : ‖δ-sin δ‖ ≤ ‖δ‖^2 := by
    rw [norm_sub_rev]
    exact norm_complex_sin_sub_self_le_sq δ hδ1
  have hc : ‖cos δ-1‖ ≤ ‖δ‖^2 := norm_complex_cos_sub_one_le_sq δ hδ1
  have hid : z^2-c^2-m+v = R+2*z*(δ-sin δ)-δ^2+(cos δ-1)*m := by dsimp only [R,δ]; ring
  have h₁ : ‖2*z*(δ-sin δ)‖ ≤ 2*‖z‖*‖δ‖^2 := by
    rw [norm_mul,norm_mul,norm_ofNat]
    exact mul_le_mul_of_nonneg_left hs (by positivity)
  have h₂ : ‖(cos δ-1)*m‖ ≤ ‖δ‖^2*t := by
    rw [norm_mul]
    exact mul_le_mul hc hm (norm_nonneg _) (sq_nonneg _)
  have hnorm : ‖z^2-c^2-m+v‖ ≤ ‖R‖+(2*‖z‖*‖δ‖^2+‖δ‖^2+‖δ‖^2*t) := by
    have hA := norm_add_le R (2*z*(δ-sin δ))
    have hB := norm_sub_le (R+2*z*(δ-sin δ)) (δ^2)
    have hC := norm_add_le (R+2*z*(δ-sin δ)-δ^2) ((cos δ-1)*m)
    rw [norm_pow] at hB
    rw [hid]
    linarith
  have hg : 2*‖z‖*‖δ‖^2+‖δ‖^2+‖δ‖^2*t ≤ 12*k*‖δ‖^2 := by
    have h₁ := mul_le_mul_of_nonneg_right hz (sq_nonneg ‖δ‖)
    have h₂ := mul_le_mul_of_nonneg_left ht1 (sq_nonneg ‖δ‖)
    have h₃ := mul_le_mul_of_nonneg_right hk (sq_nonneg ‖δ‖)
    nlinarith
  have hkpos : 0 < k := by linarith
  have hsq : k*‖δ‖^2 ≤ 64*e^4*t^2/k := by
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hδ 2) hkpos.le).trans_eq
    field_simp
    ring
  have hpow : e^3 ≤ e^4 := by
    have h := mul_nonneg (pow_nonneg (by linarith : 0 ≤ e) 3) (sub_nonneg.mpr he)
    nlinarith
  have hcoef : 32*e^3+768*e^4 ≤ 1024*e^4 := by nlinarith [pow_nonneg (by linarith : 0 ≤ e) 4]
  calc
    _ ≤ 32*e^3*t^2/k+12*(k*‖δ‖^2) := hnorm.trans (by have hr : ‖R‖ ≤ 32*e^3*t^2/k := hres; nlinarith [hr,hg])
    _ ≤ 32*e^3*t^2/k+12*(64*e^4*t^2/k) := by
      have h := mul_le_mul_of_nonneg_left hsq (by norm_num : (0 : ℝ) ≤ 12)
      linarith
    _ = (32*e^3+768*e^4)*(t^2/k) := by ring
    _ ≤ (1024*e^4)*(t^2/k) := mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = _ := by ring

end NLS.ComplexAnalysis
