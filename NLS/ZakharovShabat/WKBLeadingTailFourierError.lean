import NLS.ZakharovShabat.WKBLeadingScalarMultipliers
import NLS.ZakharovShabat.SobolevRiccatiLeadingSampling

/-! # Weighted tail error for the leading WKB expression

An Hs coefficient and an H1 sampling remainder give an H^(s+1) tail error after the actual frequency and exponential factors are included.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- The WKB leading vector's actual Fourier expression differs from
its free Fourier coefficient by one Sobolev order on both signed tails.
All multipliers use the actual displaced frequencies. -/
theorem exists_wkb_leading_tail_fourier_error
    (s K : ℕ) (b : ScalarSobolev s) (e : WeightedCoeff (Weight.sobolev 1) 2)
    (ν δ : ℤ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hν : ∀ n, ν n = (Real.pi:ℂ)*n+δ n)
    (hδ : ∀ n : ℤ, K ≤ n.natAbs → ‖δ n‖ ≤ 1)
    (hδM : ∀ n : ℤ, K ≤ n.natAbs → (1+|(n:ℝ)|)*‖δ n‖ ≤ M)
    (hνB : ∀ n : ℤ, K ≤ n.natAbs → 1+|(n:ℝ)| ≤ ‖ν n‖) :
    ∃ f : ScalarSobolev (s+1),
      (∀ n, f.val n = if K ≤ n.natAbs then
        -I*((2*I*ν n)⁻¹)^s*exp (I*ν n)*
          (-(2*I*(Real.pi:ℂ)*n)^s*b.val n+e.val n)-I*exp (I*((Real.pi:ℂ)*n))*b.val n
        else 0) ∧
      ‖f‖ ≤ (Real.exp 1*(2^s-1)+2)*M*‖b‖+Real.exp 1*‖e‖ := by
  classical
  let A : ℝ := Real.exp 1*(2^s-1)+2
  have hA : 0 ≤ A := by
    have hh : (1:ℝ) ≤ 2^s := one_le_pow₀ (by norm_num)
    dsimp [A]
    positivity
  let m₁ (n : ℤ) : ℂ := if K ≤ n.natAbs then
    I*exp (I*((Real.pi:ℂ)*n))*(exp (I*δ n)*(((Real.pi:ℂ)*n)/ν n)^s-1) else 0
  let m₂ (n : ℤ) : ℂ := if K ≤ n.natAbs then -I*((2*I*ν n)⁻¹)^s*exp (I*ν n) else 0
  have hexp (n : ℤ) : ‖exp (I*((Real.pi:ℂ)*n))‖ = 1 := by
    simp [norm_exp,Complex.mul_re,Complex.mul_im]
  have hm₁ (n : ℤ) : Weight.sobolev ((s+1:ℕ):ℝ) n*‖m₁ n‖ ≤ (A*M)*Weight.sobolev (s:ℝ) n := by
    simp only [Weight.sobolev_apply,Real.rpow_natCast]
    by_cases hn : K ≤ n.natAbs
    · simp only [m₁,if_pos hn,norm_mul,norm_I,one_mul,hexp]
      have hz1 : 1 ≤ ‖ν n‖ := by linarith [hνB n hn,abs_nonneg (n:ℝ)]
      have hh := norm_wkb_leading_relative_multiplier_sub_one_le s (ν n) ((Real.pi:ℂ)*n) (δ n)
        hz1 (hν n) (hδ n hn)
      calc
        _ ≤ (1+|(n:ℝ)|)^(s+1)*(A*‖δ n‖) := mul_le_mul_of_nonneg_left hh (by positivity)
        _ = A*(1+|(n:ℝ)|)^s*((1+|(n:ℝ)|)*‖δ n‖) := by ring
        _ ≤ A*(1+|(n:ℝ)|)^s*M := mul_le_mul_of_nonneg_left (hδM n hn) (by positivity)
        _ = _ := by ring
    · simp only [m₁,if_neg hn,norm_zero,mul_zero]
      positivity
  have hm₂ (n : ℤ) : Weight.sobolev ((s+1:ℕ):ℝ) n*‖m₂ n‖ ≤ Real.exp 1*Weight.sobolev 1 n := by
    simp only [Weight.sobolev_apply,Real.rpow_natCast,Real.rpow_one]
    by_cases hn : K ≤ n.natAbs
    · have hz1 : 1 ≤ ‖ν n‖ := by linarith [hνB n hn,abs_nonneg (n:ℝ)]
      have hex : ‖exp (I*ν n)‖ ≤ Real.exp 1 := by
        rw [hν n,mul_add,exp_add,norm_mul,hexp,one_mul]
        apply (Complex.norm_exp_le_exp_norm _).trans
        apply Real.exp_le_exp.mpr
        simpa only [norm_mul,norm_I,one_mul] using hδ n hn
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith [hνB n hn]
      have hp := pow_le_pow_left₀ (by positivity) hw s
      rw [mul_pow,one_pow] at hp
      simp only [m₂,if_pos hn,norm_mul,norm_neg,norm_I,one_mul,norm_pow]
      calc
        _ ≤ (1+|(n:ℝ)|)^(s+1)*(‖(2*I*ν n)⁻¹‖^s*Real.exp 1) := by gcongr
        _ = Real.exp 1*(1+|(n:ℝ)|)*((1+|(n:ℝ)|)^s*‖(2*I*ν n)⁻¹‖^s) := by ring
        _ ≤ Real.exp 1*(1+|(n:ℝ)|)*1 := mul_le_mul_of_nonneg_left hp (by positivity)
        _ = _ := by ring
    · simp only [m₂,if_neg hn,norm_zero,mul_zero]
      positivity
  let f₁ := WeightedCoeff.weightedMultiplier _ _ m₁ (A*M) hm₁ b
  let f₂ := WeightedCoeff.weightedMultiplier _ _ m₂ (Real.exp 1) hm₂ e
  refine ⟨f₁+f₂,?_,?_⟩
  · intro n
    simp only [WeightedCoeff.add_val,f₁,f₂,WeightedCoeff.weightedMultiplier_apply]
    by_cases hn : K ≤ n.natAbs
    · simp only [m₁,m₂,if_pos hn]
      have hz0 : ν n ≠ 0 := norm_pos_iff.mp (by have := hνB n hn; linarith [abs_nonneg (n:ℝ)])
      have hex : exp (I*ν n) = exp (I*((Real.pi:ℂ)*n))*exp (I*δ n) := by
        rw [hν n,mul_add,exp_add]
      have hratio : (2*I*ν n)⁻¹*(2*I*(Real.pi:ℂ)*n) = ((Real.pi:ℂ)*n)/ν n := by
        field_simp
      have hpow : ((2*I*ν n)⁻¹)^s*(2*I*(Real.pi:ℂ)*n)^s = (((Real.pi:ℂ)*n)/ν n)^s := by
        rw [← mul_pow,hratio]
      rw [hex]
      linear_combination -I*exp (I*((Real.pi:ℂ)*n))*exp (I*δ n)*b.val n*hpow
    · simp [m₁,m₂,hn]
  · exact (norm_add_le _ _).trans (add_le_add
      (WeightedCoeff.norm_weightedMultiplier_le _ _ m₁ (A*M) (mul_nonneg hA hM) hm₁ b)
      (WeightedCoeff.norm_weightedMultiplier_le _ _ m₂ (Real.exp 1) (Real.exp_pos 1).le hm₂ e))

end NLS.ZakharovShabat
