import NLS.ZakharovShabat.SobolevWKBDiagonalRemainder
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff
import NLS.SequenceSpaces.SobolevInversePowerBound

/-! # Sharp Sobolev tails for the diagonal remainder contribution

At full order N=s, the diagonal contribution is an H^(s+1) tail with a uniform bound on the original Sobolev ball and displacement budgets.
-/

noncomputable section
open Set Complex NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- At the full truncation order, the diagonal contribution to the
anti-discriminant error is already an H^(s+1) tail, uniformly on original
Hs balls and bounded inverse-index displacement budgets. -/
theorem exists_uniform_nlsWKB_diagonal_fourier_tail_bound
    (s : ℕ) (hs : 1 ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) →
      ∃ f : ScalarSobolev (s+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          nlsWKBInitialUpper a b s z*(nlsWKBFirstRemainder a b ha.continuous hb.continuous s z 1).1+
            nlsWKBInitialLower a b s z*(nlsWKBSecondRemainder a b ha.continuous hb.continuous s z 1).2
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K,hK,hcut⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨C,hC,hbound⟩ := exists_uniform_nlsWKB_diagonal_remainder_bound s s hs le_rfl R hR D
  refine ⟨K,hK,2*C,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let F (n : ℤ) := if K ≤ n.natAbs then
    nlsWKBInitialUpper a b s (ν n)*(nlsWKBFirstRemainder a b ha.continuous hb.continuous s (ν n) 1).1+
      nlsWKBInitialLower a b s (ν n)*(nlsWKBSecondRemainder a b ha.continuous hb.continuous s (ν n) 1).2
    else 0
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hgeom := hcut δ hδ hδM
  have hF (n : ℤ) : (1+|(n:ℝ)|)^((s+1)+1)*‖F n‖ ≤ C := by
    by_cases hn : K ≤ n.natAbs
    · have hz : 1 ≤ ‖ν n‖ := by have hh := (hgeom n hn).2; change 1 ≤ ‖(Real.pi:ℂ)*n+δ n‖; linarith [abs_nonneg (n:ℝ)]
      have hzD : |(ν n).im| ≤ D := by
        have he : (ν n).im = (δ n).im := by simp [ν,Complex.mul_im]
        rw [he]
        exact (Complex.abs_im_le_norm _).trans (hδ n)
      have hbnd := hbound ab hab a b ha hb hpa hpb hca hcb (ν n) hz hzD 1
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        have hh := (hgeom n hn).2
        change 1+|(n:ℝ)| ≤ ‖ν n‖ at hh
        linarith
      have hp := pow_le_pow_left₀ (by positivity) hw (s+2)
      rw [mul_pow,one_pow] at hp
      simp only [F,if_pos hn]
      calc
        _ ≤ (1+|(n:ℝ)|)^(s+2)*(C*‖(2*I*ν n)⁻¹‖^(s+2)) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = C*((1+|(n:ℝ)|)^(s+2)*‖(2*I*ν n)⁻¹‖^(s+2)) := by ring
        _ ≤ C*1 := mul_le_mul_of_nonneg_left hp hC
        _ = C := mul_one C
    · simpa only [F,if_neg hn,norm_zero,mul_zero] using hC
  obtain ⟨f,hf,hfn⟩ := WeightedCoeff.exists_sobolev_coeff_of_inverse_power_bound (s+1) F C hC hF
  exact ⟨f,hf,hfn⟩

end NLS.ZakharovShabat
