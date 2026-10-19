import NLS.ZakharovShabat.SobolevWKBLeadingLowerFourierTail
import NLS.ZakharovShabat.SobolevWKBNextOscillatoryComparison
import NLS.ZakharovShabat.SobolevWKBNextFreeTail
import NLS.ZakharovShabat.NLSWKBAntiErrorDecomposition

/-! # The sharp full first off-diagonal WKB remainder

The entire first-column off-diagonal remainder has an H^(N+1) tail without an extra source derivative for 1 <= N <= s.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier NLS.LinearVolterra
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The full first-column off-diagonal WKB remainder is an H^(N+1) tail,
uniformly on original Hs balls for 1 <= N <= s and throughout the physical
period. No extra derivative of the source is required. -/
theorem exists_uniform_nlsWKB_first_offDiagonal_tail_bound
    (s N : ℕ) (hN : 1 ≤ N) (hNs : N ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ∀ ha : ContDiff ℝ ∞ a, ∀ hb : ContDiff ℝ ∞ b,
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ t : Icc (0:ℝ) 1,
      ∃ f : ScalarSobolev (N+1),
        (∀ n, f.val n = if K ≤ n.natAbs then
          (nlsWKBFirstRemainder a b ha.continuous hb.continuous N ((Real.pi:ℂ)*n+δ n) t).2
          else 0) ∧ ‖f‖ ≤ C := by
  classical
  have hs := hN.trans hNs
  obtain ⟨K₀,hK₀,C₀,hC₀,hlead⟩ := exists_uniform_nlsWKB_leading_lower_fourier_tail_bound s N hs hNs R D M hR hD
  obtain ⟨K₁,_,C₁,hC₁,hnext⟩ := exists_uniform_nlsWKB_next_free_tail_bound s N hs hNs R D M hR hD
  obtain ⟨K₂,_,hcut⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨C₂,hC₂,herror⟩ := exists_uniform_nlsWKB_next_oscillatory_error_bound s N hN hNs R hR D
  let K := max K₀ (max K₁ K₂)
  refine ⟨K,hK₀.trans_le (le_max_left _ _),C₀+C₁+2*C₂,by positivity,?_⟩
  intro ab hab a b ha hb hpa hpb hca hcb δ hδD hδM t
  have hK₁ : K₁ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK₂ : K₂ ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨q₀,hq₀,hq₀n⟩ := hlead ab hab a b ha hb hpa hpb hca hcb δ hδD hδM t
  obtain ⟨q₁,hq₁,hq₁n⟩ := hnext K hK₁ ab hab a b ha hb hpa hpb hca hcb δ hδD hδM t
  let Φ := classicalPotentialOfFunctions a b ha.continuous hb.continuous
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let Y (z : ℂ) := classicalForcedKernelSolution Φ
    (classicalScalarForcing (nlsWKBLeadingScalar a b N z)
      (continuous_nlsWKBLeadingScalar a b ha hb N z)) z t
  let P (z : ℂ) := (Y z).2-nlsWKBLeadingTerm a b N z t
  let E (z : ℂ) := (nlsWKBFirstRemainder a b ha.continuous hb.continuous N z t).2-
    P z-nlsWKBNextFreeTerm a b N z t
  let F (n : ℤ) := if K ≤ n.natAbs then E (ν n) else 0
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hF (n : ℤ) : (1+|(n:ℝ)|)^((N+1)+1)*‖F n‖ ≤ C₂ := by
    by_cases hn : K ≤ n.natAbs
    · have hgeom := (hcut δ hδ hδM n (hK₂.trans hn)).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hgeom
      have hz : 1 ≤ ‖ν n‖ := by linarith [abs_nonneg (n:ℝ)]
      have hzD : |(ν n).im| ≤ D := by
        have he : (ν n).im = (δ n).im := by simp [ν,Complex.mul_im]
        rw [he]
        exact (Complex.abs_im_le_norm _).trans (hδ n)
      have hbnd : ‖E (ν n)‖ ≤ C₂*‖(2*I*ν n)⁻¹‖^(N+2) := by
        have hh := (norm_snd_le _).trans (herror ab hab a b ha hb hpa hpb hca hcb (ν n) hz hzD t)
        convert hh using 1
        congr 1
        dsimp only [E,P,Y,Φ,nlsWKBFirstRemainder]
        simp only [Prod.snd_sub]
        ring
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith
      have hp := pow_le_pow_left₀ (by positivity) hw (N+2)
      rw [mul_pow,one_pow] at hp
      simp only [F,if_pos hn]
      calc
        _ ≤ (1+|(n:ℝ)|)^(N+2)*(C₂*‖(2*I*ν n)⁻¹‖^(N+2)) :=
          mul_le_mul_of_nonneg_left hbnd (by positivity)
        _ = C₂*((1+|(n:ℝ)|)^(N+2)*‖(2*I*ν n)⁻¹‖^(N+2)) := by ring
        _ ≤ C₂*1 := mul_le_mul_of_nonneg_left hp hC₂
        _ = C₂ := mul_one C₂
    · simpa only [F,if_neg hn,norm_zero,mul_zero] using hC₂
  obtain ⟨r,hr,hrn⟩ := WeightedCoeff.exists_sobolev_coeff_of_inverse_power_bound (N+1) F C₂ hC₂ hF
  let v := Weight.sobolev ((N+1:ℕ):ℝ)
  let m (n : ℤ) : ℂ := if K ≤ n.natAbs then 1 else 0
  have hm (n : ℤ) : v n*‖m n‖ ≤ 1*v n := by
    by_cases hn : K ≤ n.natAbs
    · simp [m,hn]
    · simpa only [m,if_neg hn,norm_zero,mul_zero,one_mul] using (v.positive n).le
  let q := WeightedCoeff.weightedMultiplier v v m 1 hm q₀
  have hqn : ‖q‖ ≤ C₀ := by
    have hh := WeightedCoeff.norm_weightedMultiplier_le v v m 1 zero_le_one hm q₀
    have hh' : ‖q‖ ≤ ‖q₀‖ := by simpa only [one_mul] using hh
    exact hh'.trans hq₀n
  have hq (n : ℤ) : q.val n = if K ≤ n.natAbs then P (ν n) else 0 := by
    change m n*q₀.val n = _
    rw [hq₀ n]
    by_cases hn : K ≤ n.natAbs
    · have hn₀ : K₀ ≤ n.natAbs := (le_max_left _ _).trans hn
      simp only [m,if_pos hn,if_pos hn₀,one_mul,P,Y,Φ,ν]
    · simp [m,hn]
  refine ⟨q+q₁+r,?_,?_⟩
  · intro n
    rw [WeightedCoeff.add_val,WeightedCoeff.add_val,hq n,hq₁ n,hr n]
    by_cases hn : K ≤ n.natAbs
    · simp only [if_pos hn,F,E,ν]
      ring
    · simp [F,hn]
  · exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      (add_le_add (add_le_add hqn hq₁n) hrn))

end NLS.ZakharovShabat
