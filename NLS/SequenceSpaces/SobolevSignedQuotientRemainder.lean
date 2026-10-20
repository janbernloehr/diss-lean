import NLS.SequenceSpaces.SobolevPowerMultiplier
import Mathlib.Tactic.LinearCombination

/-! # Sobolev remainders under a signed quotient

An order-one inverse normalization error preserves the one-derivative Fourier remainder with an explicit norm bound.
-/

noncomputable section
open Complex
open scoped ENNReal
namespace NLS.WeightedCoeff
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Dividing a signed Fourier leading term plus a smoother error by a
product with an order-one inverse normalization error preserves the full
one-derivative gain, with an explicit norm bound. -/
theorem exists_sobolev_signed_quotient_remainder
    (r : ℝ) (a : WeightedCoeff (Weight.sobolev r) p)
    (e : WeightedCoeff (Weight.sobolev (r+1)) p)
    (P sign : ℤ → ℂ) (hsign : ∀ n, (sign n)^2 = 1) (hsignnorm : ∀ n, ‖sign n‖ = 1)
    (q : WeightedCoeff (Weight.sobolev 1) ⊤)
    (hqval : ∀ n, q.val n = (P n)⁻¹-sign n) :
    ∃ f : WeightedCoeff (Weight.sobolev (r+1)) p,
      (∀ n, f.val n = (e.val n+I*sign n*a.val n)/(2*P n)-(I/2)*a.val n) ∧
      ‖f‖ ≤ ((‖q‖+1)*‖e‖+‖q‖*‖a‖)/2 := by
  have hq (n : ℤ) : (1+|(n:ℝ)|)*‖q.val n‖ ≤ ‖q‖ := by
    have h := (le_div_iff₀ ((Weight.sobolev 1).positive n)).mp
      (norm_apply_le (Weight.sobolev 1) ⊤ q n)
    simpa only [Weight.sobolev_apply,Real.rpow_one,mul_comm] using h
  have hq₀ (n : ℤ) : ‖q.val n‖ ≤ ‖q‖ := by
    nlinarith [hq n,abs_nonneg (n:ℝ),norm_nonneg (q.val n)]
  have hP (n : ℤ) : ‖(P n)⁻¹‖ ≤ ‖q‖+1 := by
    have he : (P n)⁻¹ = q.val n+sign n := by rw [hqval]; ring
    rw [he]
    exact (norm_add_le _ _).trans (by rw [hsignnorm]; exact add_le_add (hq₀ n) le_rfl)
  let w := Weight.sobolev (r+1)
  have hm (n : ℤ) : w n*‖(P n)⁻¹‖ ≤ (‖q‖+1)*w n := by
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP n) (w.positive n).le
  let T₀ := weightedMultiplierCLM (p := p) w w (fun n => (P n)⁻¹) (‖q‖+1) (by positivity) hm
  obtain ⟨T₁,hT₁,hT₁n⟩ := exists_sobolev_power_multiplier (p := p) r 1
    (fun n => sign n*q.val n) ‖q‖ (norm_nonneg _) (by
      intro n
      simpa only [Real.rpow_one,norm_mul,hsignnorm,one_mul] using hq n)
  let f := (1/2:ℂ) • T₀ e+(I/2:ℂ) • T₁ a
  refine ⟨f,?_,?_⟩
  · intro n
    simp only [f,add_val,smul_val,T₀,weightedMultiplierCLM_apply,hT₁,hqval,div_eq_mul_inv,mul_inv_rev]
    have h := hsign n
    linear_combination -(I/2)*a.val n*h
  · have hT₀ : ‖T₀ e‖ ≤ (‖q‖+1)*‖e‖ :=
      norm_weightedMultiplier_le w w (fun n => (P n)⁻¹) (‖q‖+1) (by positivity) hm e
    have hT₁a : ‖T₁ a‖ ≤ ‖q‖*‖a‖ :=
      (T₁.le_opNorm a).trans (mul_le_mul_of_nonneg_right hT₁n (norm_nonneg _))
    have hn := norm_add_le ((1/2:ℂ) • T₀ e) ((I/2:ℂ) • T₁ a)
    simp only [norm_smul,norm_div,norm_one,norm_I,norm_ofNat] at hn
    change ‖f‖ ≤ _ at hn
    exact hn.trans (by nlinarith)

end NLS.WeightedCoeff
