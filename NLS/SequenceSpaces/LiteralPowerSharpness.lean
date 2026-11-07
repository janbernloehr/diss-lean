import NLS.SequenceSpaces.PositiveSobolevReverseComparison

/-! Failure of stronger bracket bounds implies failure of EVERY
stronger literal positive-frequency power bound. -/
noncomputable section
open Set
namespace NLS.Coeff

theorem exists_literal_power_frequency_lower_bound
    {E : Type*} (T : Set E) (f : ℕ+ → E → ℂ) (α : ℝ) (hα0 : -1<α) (hα1 : α<1)
    (hsharp : ∀ r : ℝ, α<r → ∀ B : ℝ, 0≤B → ∀ K : ℕ,
      ∃ a∈T, ∃ n : ℕ+, K≤(n:ℤ).natAbs ∧ B<Weight.sobolev r (n:ℤ)*‖f n a‖)
    (γ : ℝ) (hγ : γ< -α) (M : ℝ) (hM : 0≤M) (K : ℕ) :
    ∃ a∈T, ∃ n : ℕ+, K≤(n:ℤ).natAbs ∧ M<(n:ℝ)^(-γ)*‖f n a‖ := by
  obtain ⟨r,hr0,hr1⟩ := exists_between (lt_min (by linarith : α< -γ) hα1)
  have hrγ : r< -γ := hr1.trans_le (min_le_left _ _)
  have hrone : r<1 := hr1.trans_le (min_le_right _ _)
  obtain ⟨a,ha,n,hn,hlarge⟩ := hsharp r hr0 (2*M) (by positivity) K
  have hp := sobolev_le_two_positive_power r (by linarith) hrone.le n
  have hn1 : (1:ℝ)≤n := by exact_mod_cast n.pos
  have hpow := Real.rpow_le_rpow_of_exponent_le hn1 hrγ.le
  have hb := mul_le_mul_of_nonneg_right (hp.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℝ)≤2))) (norm_nonneg (f n a))
  exact ⟨a,ha,n,hn,by nlinarith⟩

end NLS.Coeff
