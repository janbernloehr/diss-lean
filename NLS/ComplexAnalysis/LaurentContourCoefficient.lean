import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Tactic

/-! # Normalized Laurent contour coefficients and a uniform weighted contour-error bound. -/

noncomputable section
set_option autoImplicit false
open Set Metric Complex Filter Topology
open scoped ContDiff ComplexConjugate
namespace NLS.ComplexAnalysis
theorem circleIntegrable_zero_zpow (k : ℤ) (R : ℝ) (hR : 0 < R) :
    CircleIntegrable (fun z : ℂ => z^k) 0 R := by
  have hc : ContinuousOn (fun z : ℂ => z^k) (sphere (0 : ℂ) R) := by
    apply continuousOn_id.zpow₀ k
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact Or.inl (norm_pos_iff.mp (hn.symm ▸ hR))
  exact hc.circleIntegrable hR.le

theorem circleIntegral_zero_zpow (k : ℤ) (R : ℝ) (hR : 0 < R) :
    (∮ z in C((0 : ℂ),R), z^k) = if k = -1 then 2*Real.pi*I else 0 := by
  by_cases hk : k = -1
  · subst k
    simpa only [↓reduceIte, zpow_neg_one, sub_zero] using
      circleIntegral.integral_sub_inv_of_mem_ball (mem_ball_self hR : (0 : ℂ) ∈ ball 0 R)
  · simpa only [hk, ↓reduceIte, sub_zero] using
      circleIntegral.integral_sub_zpow_of_ne hk (0 : ℂ) (0 : ℂ) R

theorem normalized_circleIntegral_const_mul_zpow (c : ℂ) (k : ℤ) (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ),R), c*z^k) =
      if k = -1 then 2*c else 0 := by
  rw [circleIntegral.integral_const_mul, circleIntegral_zero_zpow k R hR]
  split_ifs
  · have hn : (Real.pi : ℂ)*I ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  · simp

theorem normalized_circleIntegral_weighted_zpow (c : ℂ) (k : ℤ) (m : ℕ)
    (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ),R), z^m*(c*z^k)) =
      if (m : ℤ)+k = -1 then 2*c else 0 := by
  have he : (∮ z in C((0 : ℂ),R), z^m*(c*z^k)) =
      ∮ z in C((0 : ℂ),R), c*z^((m : ℤ)+k) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hz0 : z ≠ 0 := norm_pos_iff.mp (hn.symm ▸ hR)
    change z^m*(c*z^k) = c*z^((m : ℤ)+k)
    rw [zpow_add₀ hz0, zpow_natCast]
    ring
  rw [he]
  exact normalized_circleIntegral_const_mul_zpow c _ R hR


theorem circleIntegrable_weighted_zpow (c : ℂ) (k : ℤ) (m : ℕ)
    (R : ℝ) (hR : 0 < R) :
    CircleIntegrable (fun z : ℂ => z^m*(c*z^k)) 0 R := by
  have hpow : ContinuousOn (fun z : ℂ => z^k) (sphere (0 : ℂ) R) := by
    apply continuousOn_id.zpow₀ k
    intro z hz
    have hn : ‖z‖ = R := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    exact Or.inl (norm_pos_iff.mp (hn.symm ▸ hR))
  exact ((continuousOn_id.pow m).mul (continuousOn_const.mul hpow)).circleIntegrable hR.le

theorem normalized_circleIntegral_weighted_finsum {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (k : ι → ℤ) (m : ℕ) (R : ℝ) (hR : 0 < R) :
    ((Real.pi : ℂ)*I)⁻¹ * (∮ z in C((0 : ℂ),R), z^m*(∑ i ∈ S, c i*z^(k i))) =
      ∑ i ∈ S, if (m : ℤ)+k i = -1 then 2*c i else 0 := by
  have he : (fun z : ℂ => z^m*(∑ i ∈ S, c i*z^(k i))) =
      fun z => ∑ i ∈ S, z^m*(c i*z^(k i)) := by funext z; rw [Finset.mul_sum]
  rw [he, circleIntegral.integral_fun_sum
    (fun i _ => circleIntegrable_weighted_zpow (c i) (k i) m R hR), Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => normalized_circleIntegral_weighted_zpow (c i) (k i) m R hR


theorem sum_rectangle_ite_eq_antidiagonal {A : Type*} [AddCommMonoid A]
    (M n : ℕ) (hn : n < M) (f : ℕ × ℕ → A) :
    (∑ ij ∈ Finset.range M ×ˢ Finset.range M,
      if ij.1+ij.2=n then f ij else 0) = ∑ ij ∈ Finset.antidiagonal n, f ij := by
  rw [← Finset.sum_filter]
  congr 1
  ext ij
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_antidiagonal]
  omega


theorem norm_weighted_circle_integral_sub_model_le (f P : ℂ → ℂ) (m : ℕ) (r C : ℝ)
    (hr : 0 < r) (hf : CircleIntegrable (fun z => z^m*f z) 0 (r^2))
    (hP : CircleIntegrable (fun z => z^m*P z) 0 (r^2))
    (hbound : ∀ z ∈ sphere (0 : ℂ) (r^2), r^(2*m+4)*‖f z-P z‖ ≤ C) :
    ‖((Real.pi : ℂ)*I)⁻¹*(∮ z in C((0 : ℂ),r^2), z^m*f z) -
      ((Real.pi : ℂ)*I)⁻¹*(∮ z in C((0 : ℂ),r^2), z^m*P z)‖ ≤ 2*C/r^2 := by
  have hR : 0 < r^2 := sq_pos_of_pos hr
  have he : (fun z : ℂ => z^m*(f z-P z)) = fun z => z^m*f z-z^m*P z := by
    funext z
    ring
  have hint : (∮ z in C((0 : ℂ),r^2), z^m*(f z-P z)) =
      (∮ z in C((0 : ℂ),r^2), z^m*f z) - ∮ z in C((0 : ℂ),r^2), z^m*P z := by
    rw [he, circleIntegral.integral_sub hf hP]
  have hb : ‖∮ z in C((0 : ℂ),r^2), z^m*(f z-P z)‖ ≤
      2*Real.pi*(r^2)*(C/r^4) := by
    apply circleIntegral.norm_integral_le_of_norm_le_const hR.le
    intro z hz
    have hn : ‖z‖ = r^2 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    rw [norm_mul, norm_pow, hn]
    apply (le_div_iff₀ (pow_pos hr 4)).mpr
    calc
      _ = r^(2*m+4)*‖f z-P z‖ := by rw [pow_add, pow_mul]; ring
      _ ≤ C := hbound z hz
  rw [← mul_sub, ← hint, norm_mul]
  have hn : ‖((Real.pi : ℂ)*I)⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos, norm_I, mul_one]
  rw [hn]
  apply (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr Real.pi_pos.le)).trans_eq
  have hr0 := hr.ne'
  field_simp


theorem circleIntegrable_weighted_finsum {ι : Type*} (S : Finset ι)
    (c : ι → ℂ) (k : ι → ℤ) (m : ℕ) (R : ℝ) (hR : 0 < R) :
    CircleIntegrable (fun z : ℂ => z^m*(∑ i ∈ S, c i*z^(k i))) 0 R := by
  convert! CircleIntegrable.sum S
    (fun i _ => circleIntegrable_weighted_zpow (c i) (k i) m R hR) using 1
  funext z
  simp only [Finset.mul_sum, Finset.sum_apply]


end NLS.ComplexAnalysis
