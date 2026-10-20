import NLS.ZakharovShabat.WKBBoundedFrequencyCutoff
import NLS.ZakharovShabat.SobolevWKBDiagonalOscillatoryTail
import NLS.SequenceSpaces.SobolevInversePowerBound

/-! # The corrected leading diagonal tail

Removing the explicit phase primitive leaves a one-order smoother tail in the actual leading upper response.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The actual upper response to the leading WKB forcing differs from
its explicit diagonal phase primitive by an H^(N+1) tail. The estimate is uniform on
original Hs balls through N=s and throughout the physical period. -/
theorem exists_uniform_nlsWKB_leading_diagonal_fourier_tail_bound_of_bounded_displacement
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      ∀ t : Icc (0:ℝ) 1,
      ∃ f : ScalarSobolev (N+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          (classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
              (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t).1-
            nlsWKBDiagonalPhasePrimitive a b N z t else 0) ∧ ‖f‖ ≤ C := by
  classical
  obtain ⟨K₀,hK₀,C₀,hC₀,hosc⟩ := exists_uniform_nlsWKB_diagonal_oscillatory_tail_bound_of_bounded_displacement s N hs hNs R D hR hD
  obtain ⟨K₁,_,hcut⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨C₁,hC₁,herr⟩ := exists_uniform_nlsWKB_leading_diagonal_approximation_error_bound s N hs hNs R hR D
  let K := max K₀ K₁
  refine ⟨K,hK₀.trans_le (le_max_left _ _),C₀+2*C₁,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD t
  obtain ⟨q,hq,hqn⟩ := hosc K' ((le_max_left _ _).trans hK') ab hab a b ha hb hpa hpb hca hcb δ hδD t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let Y (z : ℂ) := (classicalForcedKernelSolution Φ
    (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
      (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t).1
  let Q (z : ℂ) := ((2*I*z)⁻¹)^(N+1)*nlsWKBDiagonalOscillatoryIntegral a b N z t
  let F (n : ℤ) := if K' ≤ n.natAbs then Y (ν n)-nlsWKBDiagonalPhasePrimitive a b N (ν n) t-Q (ν n) else 0
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hF (n : ℤ) : (1+|(n:ℝ)|)^((N+1)+1)*‖F n‖ ≤ C₁ := by
    by_cases hn : K' ≤ n.natAbs
    · have hgeom := (hcut δ hδ n ((le_max_right _ _).trans (hK'.trans hn))).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hgeom
      have hz : 1 ≤ ‖ν n‖ := by linarith [abs_nonneg (n:ℝ)]
      have hzD : |(ν n).im| ≤ D := by
        have he : (ν n).im = (δ n).im := by simp [ν,Complex.mul_im]
        rw [he]
        exact (Complex.abs_im_le_norm _).trans (hδ n)
      have hbnd := herr ab hab a b ha hb hpa hpb hca hcb (ν n) hz hzD t
      rw [nlsWKBLeadingDiagonalApproximation_eq_phase_add_oscillatory a b ha hb,sub_add_eq_sub_sub] at hbnd
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith
      have hp := pow_le_pow_left₀ (by positivity) hw (N+2)
      rw [mul_pow,one_pow] at hp
      simp only [F,if_pos hn]
      calc
        _ ≤ (1+|(n:ℝ)|)^(N+2)*(C₁*‖(2*I*ν n)⁻¹‖^(N+2)) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = C₁*((1+|(n:ℝ)|)^(N+2)*‖(2*I*ν n)⁻¹‖^(N+2)) := by ring
        _ ≤ C₁*1 := mul_le_mul_of_nonneg_left hp hC₁
        _ = C₁ := mul_one C₁
    · simpa only [F,if_neg hn,norm_zero,mul_zero] using hC₁
  obtain ⟨r,hr,hrn⟩ := WeightedCoeff.exists_sobolev_coeff_of_inverse_power_bound (N+1) F C₁ hC₁ hF
  refine ⟨q+r,?_,(norm_add_le q r).trans (add_le_add hqn hrn)⟩
  intro n
  rw [WeightedCoeff.add_val,hq n,hr n]
  by_cases hn : K' ≤ n.natAbs
  · simp only [if_pos hn,F,ν,Y,Q,Φ]
    ring
  · simp [F,hn]

/-- The actual upper response to the leading WKB forcing differs from
its explicit diagonal phase primitive by an H^(N+1) tail. The estimate is uniform on
original Hs balls through N=s and throughout the physical period. -/
theorem exists_uniform_nlsWKB_leading_diagonal_fourier_tail_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ t : Icc (0:ℝ) 1,
      ∃ f : ScalarSobolev (N+1),
        (∀ n, f.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          (classicalForcedKernelSolution (classicalPotentialOfFunctions a b ha.continuous hb.continuous)
            (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
              (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t).1-
            nlsWKBDiagonalPhasePrimitive a b N z t else 0) ∧ ‖f‖ ≤ C := by
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_leading_diagonal_fourier_tail_bound_of_bounded_displacement s N hs hNs R D hR hD
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD _hδM t
  exact h K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD t

end NLS.ZakharovShabat
