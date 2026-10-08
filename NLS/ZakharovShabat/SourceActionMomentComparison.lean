import NLS.ZakharovShabat.RefinedH1ActionBound

/-! # Comparing action moments at a freely chosen frequency threshold -/
noncomputable section
namespace NLS.ZakharovShabat

/-- A frequency split bounds a lower moment by the top moment and total mass. -/
theorem threshold_mul_sq_le_top_add (m : ℕ) (hm : 1 ≤ m) (B w : ℝ)
    (hB : 0 ≤ B) (hw : 0 ≤ w) :
    B^(2*(m-1))*w^2 ≤ w^(2*m)+B^(2*m) := by
  have he : 2*(m-1)+2 = 2*m := by omega
  by_cases h : w ≤ B
  · have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw h 2)
      (pow_nonneg hB (2*(m-1)))
    rw [← pow_add,he] at hp
    exact hp.trans (le_add_of_nonneg_left (pow_nonneg hw _))
  · have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hB (le_of_not_ge h) (2*(m-1)))
      (sq_nonneg w)
    rw [← pow_add,he] at hp
    exact hp.trans (le_add_of_nonneg_right (pow_nonneg hB _))

/-- Weighted ℓ¹ interpolation without roots or division, including zero total action. -/
theorem sourceWeightedAction_threshold_comparison (m : ℕ) (hm : 1 ≤ m)
    (a : realTypeHigherSobolevSourceLocus m) (B : ℝ) (hB : 0 ≤ B) :
    B^(2*(m-1))*(∑' n : ℤ, sourceWeightedActionTerm
      ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 1 n) ≤
    (∑' n : ℤ, sourceWeightedActionTerm ⟨higherSobolevSourceInclusion m a.val,a.property⟩ m n)+
      B^(2*m)*(∑' n : ℤ, sourceWeightedActionTerm
        ⟨higherSobolevSourceInclusion m a.val,a.property⟩ 0 n) := by
  let ψ : realTypeSourceSubmodule 2 := ⟨higherSobolevSourceInclusion m a.val,a.property⟩
  have htop : Summable (sourceWeightedActionTerm ψ m) := sourceWeightedAction_summable_on_Hm m hm a
  have hlow : Summable (sourceWeightedActionTerm ψ 1) := by
    simpa only [sourceH1RealSource_realHigherSobolevToH1] using
      sourceH1_weightedActions_summable (realHigherSobolevToH1 m hm a)
  have hmass : Summable (sourceWeightedActionTerm ψ 0) := by
    change Summable (fun n => sourceWeightedActionTerm ψ 0 n)
    simpa only [sourceWeightedActionTerm,Nat.mul_zero,pow_zero,one_mul,norm_sourceRealAction]
      using sourceRealActions_summable ψ
  have hpoint (n : ℤ) : B^(2*(m-1))*sourceWeightedActionTerm ψ 1 n ≤
      sourceWeightedActionTerm ψ m n+B^(2*m)*sourceWeightedActionTerm ψ 0 n := by
    have h := mul_le_mul_of_nonneg_right
      (threshold_mul_sq_le_top_add m hm B (1+|((2*n:ℤ):ℝ)*Real.pi|) hB (by positivity))
      (norm_nonneg (sourceRealAction (by simp) (by norm_num) ψ.val ψ.property n))
    simpa only [sourceWeightedActionTerm,Nat.mul_one,Nat.mul_zero,pow_zero,one_mul,
      add_mul,mul_assoc] using h
  have h := (hlow.mul_left (B^(2*(m-1)))).tsum_le_tsum hpoint
    (htop.add (hmass.mul_left (B^(2*m))))
  simpa only [Summable.tsum_add htop (hmass.mul_left (B^(2*m))),tsum_mul_left] using h

end NLS.ZakharovShabat
