import NLS.KdV.HillL2QuadraticTrace

/-! # The finite weighted action head is bounded by the actual quadratic trace. -/

noncomputable section
set_option autoImplicit false
open Set Complex Filter Topology
open scoped ENNReal
namespace NLS.KdV

theorem hillWeightedAction_head_bound (w : SpectralWeight) (p : RealHillWeightedPotential w)
    (hmean : p.val.val 0=0) (K : ℕ) :
    (∑ n ∈ Finset.range (K+1), hillWeightedActionTerm w p n) ≤
      (w (2*(K : ℤ)))^2*((1/2 : ℝ)*‖p.val‖^2) := by
  let q0 : WeightedCoeff SpectralWeight.one.doubleIndex.toWeight 2 := hillForgetWeight w.doubleIndex 2 p.val
  have hcoef (k : ℤ) : q0.val k = p.val.val k := hillForgetWeight_apply _ _ _ _
  have hr0 : IsRealHillPotential (SpectralWeight.one.doubleIndex.toCoeff q0) := by
    intro k
    simpa only [SpectralWeight.toCoeff_apply,hcoef] using p.property k
  have hm0 : q0.val 0=0 := (hcoef 0).trans hmean
  have ht := (hasSum_hillPeriodOneActions_quadratic_l2 ⟨q0,hr0⟩ hm0)
  let f : ℕ → ℝ := fun n => (2*Real.pi*(n : ℝ))*hillPeriodOneAction w p.val p.property n
  have he (k : ℕ) : (2*Real.pi*(k+1 : ℕ))*hillPeriodOneAction SpectralWeight.one q0 hr0 (k+1)=f (k+1) := by
    rw [hillPeriodOneAction_eq_of_coeff_eq SpectralWeight.one w q0 p.val hr0 p.property hcoef (k+1)]
  rw [funext he] at ht
  have hf0 (n : ℕ) : 0≤f n := by
    by_cases hn : n=0
    · subst n
      simp [f]
    · exact mul_nonneg (by positivity) (hillPeriodOneAction_nonneg w p.val p.property n (by omega))
  have hfs : Summable f := (summable_nat_add_iff 1).mp ht.summable
  have hz : f 0=0 := by simp [f]
  have hsum : (∑' n : ℕ, f n)=(1/2 : ℝ)*‖q0‖^2 := by
    have h := hfs.sum_add_tsum_nat_add 1
    simpa only [Finset.sum_range_one,hz,zero_add,ht.tsum_eq] using h.symm
  have hweight (n : ℕ) (hn : n∈Finset.range (K+1)) : w (2*(n : ℤ))≤w (2*(K : ℤ)) := by
    have hnk : n≤K := by have h := Finset.mem_range.mp hn; omega
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using w.monotone_nat (Nat.mul_le_mul_left 2 hnk)
  calc
    _ ≤ ∑ n ∈ Finset.range (K+1), (w (2*(K : ℤ)))^2*f n := by
      apply Finset.sum_le_sum
      intro n hn
      dsimp only [hillWeightedActionTerm]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (w.positive _).le (hweight n hn) 2) (hf0 n)
    _ = (w (2*(K : ℤ)))^2*∑ n ∈ Finset.range (K+1), f n := (Finset.mul_sum _ _ _).symm
    _ ≤ (w (2*(K : ℤ)))^2*(∑' n : ℕ, f n) :=
      mul_le_mul_of_nonneg_left (hfs.sum_le_tsum _ (fun n _ => hf0 n)) (sq_nonneg _)
    _ = (w (2*(K : ℤ)))^2*((1/2 : ℝ)*‖q0‖^2) := by rw [hsum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      have hnorm : ‖q0‖≤‖p.val‖ := norm_hillForgetWeight_le _ _ _
      nlinarith [norm_nonneg q0]

end NLS.KdV
