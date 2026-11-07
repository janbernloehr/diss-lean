import NLS.SequenceSpaces.WeightedFrequencyRemainders

/-! Literal positive powers and Sobolev brackets have the same
frequency decay on the source interval of exponents [-1,1]. -/
noncomputable section
open Filter Topology
namespace NLS.Coeff

theorem positive_power_le_two_sobolev
    (r : ℝ) (hr0 : -1≤r) (_hr1 : r≤1) (n : ℕ+) :
    (n:ℝ)^r≤2*Weight.sobolev r (n:ℤ) := by
  have hn : (1:ℝ)≤n := by exact_mod_cast n.pos
  have hn0 : (0:ℝ)<n := by linarith
  have hw : Weight.sobolev r (n:ℤ)=(1+(n:ℝ))^r := by
    simp only [Weight.sobolev_apply,Int.cast_natCast,abs_of_pos hn0]
  rw [hw]
  by_cases hr : 0≤r
  · have h := Real.rpow_le_rpow hn0.le (show (n:ℝ)≤1+n by linarith) hr
    nlinarith [Real.rpow_nonneg (by linarith : (0:ℝ)≤1+n) r]
  · have hd : 0≤ -r := by linarith
    have hd1 : -r≤1 := by linarith
    have htwo : (2:ℝ)^(-r)≤2 := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) hd1
    have he : (1+(n:ℝ))^(-r)≤2*(n:ℝ)^(-r) := by
      calc
        _ ≤ (2*(n:ℝ))^(-r) := Real.rpow_le_rpow (by positivity) (by linarith) hd
        _ = (2:ℝ)^(-r)*(n:ℝ)^(-r) := Real.mul_rpow (by norm_num) hn0.le
        _ ≤ _ := mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hn0.le _)
    have hi : 1/((n:ℝ)^(-r))≤2/((1+(n:ℝ))^(-r)) :=
      (div_le_div_iff₀ (Real.rpow_pos_of_pos hn0 _) (Real.rpow_pos_of_pos (by positivity : (0:ℝ)<1+n) _)).mpr
        (by simpa only [one_mul] using he)
    simpa only [one_div,one_mul,div_eq_mul_inv,Real.rpow_neg hn0.le,
      Real.rpow_neg (by positivity : (0:ℝ)≤1+n),inv_inv] using hi

theorem tendsto_positive_power_of_sobolev
    (r : ℝ) (hr0 : -1≤r) (hr1 : r≤1) (f : ℕ+ → ℂ)
    (h : Tendsto (fun m : ℕ => Weight.sobolev r ((m+1:ℕ):ℤ)*‖f ⟨m+1,by omega⟩‖) atTop (𝓝 0)) :
    Tendsto (fun m : ℕ => (m+1:ℝ)^r*‖f ⟨m+1,by omega⟩‖) atTop (𝓝 0) := by
  have ht := h.const_mul 2
  rw [mul_zero] at ht
  apply squeeze_zero (fun _ => mul_nonneg (Real.rpow_nonneg (by positivity) _) (norm_nonneg _)) _ ht
  intro m
  have hh := mul_le_mul_of_nonneg_right (positive_power_le_two_sobolev r hr0 hr1 ⟨m+1,by omega⟩)
    (norm_nonneg (f ⟨m+1,by omega⟩))
  change (((m+1:ℕ):ℝ)^r)*‖f ⟨m+1,by omega⟩‖≤
    (2*Weight.sobolev r ((m+1:ℕ):ℤ))*‖f ⟨m+1,by omega⟩‖ at hh
  simpa only [Nat.cast_add,Nat.cast_one,mul_assoc] using hh

end NLS.Coeff
