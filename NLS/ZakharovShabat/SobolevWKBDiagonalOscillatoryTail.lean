import NLS.ZakharovShabat.WKBBoundedFrequencyCutoff
import NLS.ZakharovShabat.NLSWKBDiagonalPhaseDecomposition
import NLS.Fourier.DiagonalOscillatorySampling
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff
import NLS.SequenceSpaces.WeightedMultiplier

/-! # The diagonal oscillatory Sobolev tail

The sampled diagonal correction belongs to H^(N+1) with uniform cutoff and norm bounds on original Hs balls.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The oscillatory part of the leading diagonal approximation is
an H^(N+1) tail, uniformly on original Hs balls through N=s and over the
whole physical period. -/
theorem exists_uniform_nlsWKB_diagonal_oscillatory_tail_bound_of_bounded_displacement
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R D : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      ∀ t : Icc (0:ℝ) 1,
      ∃ q : ScalarSobolev (N+1),
        (∀ n, q.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          ((2*I*z)⁻¹)^(N+1)*nlsWKBDiagonalOscillatoryIntegral a b N z t
          else 0) ∧ ‖q‖ ≤ C := by
  classical
  obtain ⟨K,hK,hcut⟩ := exists_wkb_bounded_frequency_cutoff D hD
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  obtain ⟨Ld,hLd,hder⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s 1 hs R hR
  refine ⟨K,hK,(A*Real.exp (3*D)+Real.exp (5*D)*Ld)*L,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD t
  let ρ := nlsRiccatiDensity a b N
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hρL2 := memLp_two_interval hρ 0 1 (by norm_num : (0:ℝ) ≤ 1)
  have hda : Continuous (deriv a) := ha.continuous_deriv (by simp)
  have hd : (∫ x in (0:ℝ)..1, ‖deriv a x‖) ≤ Ld := by
    have hi := NLS.ComplexAnalysis.integral_norm_le_sqrt_length_mul_L2 (deriv a) 1 (by norm_num)
      (memLp_two_interval hda 0 1 (by norm_num))
    simp only [Real.sqrt_one,one_mul] at hi
    apply hi.trans
    simpa only [nlsRiccatiDensity_one,Pi.neg_apply,norm_neg] using
      hder (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca
  have hρn : ‖unitIntervalMemLpCoefficients ρ hρL2‖ ≤ L := by
    have he := norm_sq_unitIntervalMemLpCoefficients ρ hρL2
    have he' : ‖unitIntervalMemLpCoefficients ρ hρL2‖ =
        Real.sqrt (∫ x in (0:ℝ)..1, ‖ρ x‖^2) := by
      rw [← he,Real.sqrt_sq (norm_nonneg _)]
    rw [he']
    exact hL2 ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨q,hq,hqn⟩ := exists_diagonal_oscillatory_lattice_coefficients
    ρ (deriv a) hρ hda hρL2 (a t) δ t
  have hqbound : ‖q‖ ≤ (A*Real.exp (3*D)+Real.exp (5*D)*Ld)*L := by
    apply hqn.trans
    apply mul_le_mul _ hρn (norm_nonneg _) (by positivity)
    apply add_le_add
    · exact mul_le_mul (hpot ab hab a b ha hb hpa hpb hca hcb t)
        (Real.exp_le_exp.mpr (by linarith)) (Real.exp_pos _).le hA
    · exact mul_le_mul (Real.exp_le_exp.mpr (by linarith)) hd
        (intervalIntegral.integral_nonneg (by norm_num) (fun x _ => norm_nonneg _)) (Real.exp_pos _).le
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let m (n : ℤ) := if K' ≤ n.natAbs then ((2*I*ν n)⁻¹)^(N+1) else 0
  let v := Weight.sobolev ((N+1:ℕ):ℝ)
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hm (n : ℤ) : v n*‖m n‖ ≤ 1*Weight.one n := by
    by_cases hn : K' ≤ n.natAbs
    · have hh := (hcut δ hδ n (hK'.trans hn)).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hh
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        have hpos : (0:ℝ) < 1+|(n:ℝ)| := by positivity
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith [norm_nonneg (ν n)]
      have hp := pow_le_pow_left₀ (by positivity) hw (N+1)
      simpa only [v,Weight.sobolev_apply,Real.rpow_natCast,m,if_pos hn,
        norm_pow,Weight.one_apply,one_mul,mul_pow,one_pow] using hp
    · simp [m,hn,v]
  let q₀ := (WeightedCoeff.weightIsometry Weight.one 2).symm q
  have hq₀ (n : ℤ) : q₀.val n = q n := by
    change q n/(Weight.one n:ℂ) = q n
    simp
  let f := WeightedCoeff.weightedMultiplier Weight.one v m 1 hm q₀
  refine ⟨f,?_,?_⟩
  · intro n
    change m n*q₀.val n = _
    rw [hq₀,hq n]
    by_cases hn : K' ≤ n.natAbs
    · simp only [m,if_pos hn,ν,nlsWKBDiagonalOscillatoryIntegral,ρ]
    · simp [m,hn]
  · have hn := WeightedCoeff.norm_weightedMultiplier_le Weight.one v m 1 zero_le_one hm q₀
    simpa only [one_mul,LinearIsometryEquiv.norm_map] using hn.trans (by
      simpa only [one_mul,LinearIsometryEquiv.norm_map,q₀] using hqbound)

/-- The oscillatory part of the leading diagonal approximation is
an H^(N+1) tail, uniformly on original Hs balls through N=s and over the
whole physical period. -/
theorem exists_uniform_nlsWKB_diagonal_oscillatory_tail_bound
    (s N : ℕ) (hs : 1 ≤ s) (hNs : N ≤ s) (R D M : ℝ) (hR : 0 ≤ R) (hD : 0 ≤ D) :
    ∃ K : ℕ, 0 < K ∧ ∃ C : ℝ, 0 ≤ C ∧
      ∀ K' : ℕ, K ≤ K' → ∀ ab : SobolevSource s, ‖ab‖ ≤ R → ∀ a b : ℝ → ℂ,
      ContDiff ℝ ∞ a → ContDiff ℝ ∞ b →
      Function.Periodic a 1 → Function.Periodic b 1 →
      (∀ j, ab.1.val j = periodOneCoefficient a j) →
      (∀ j, ab.2.val j = periodOneCoefficient b j) →
      ∀ δ : NLS.Coeff ⊤, ‖δ‖ ≤ D →
      (∀ n : ℤ, (1+|(n:ℝ)|)*‖δ n‖ ≤ M) → ∀ t : Icc (0:ℝ) 1,
      ∃ q : ScalarSobolev (N+1),
        (∀ n, q.val n = if K' ≤ n.natAbs then
          let z := (Real.pi:ℂ)*n+δ n
          ((2*I*z)⁻¹)^(N+1)*nlsWKBDiagonalOscillatoryIntegral a b N z t
          else 0) ∧ ‖q‖ ≤ C := by
  obtain ⟨K,hK,C,hC,h⟩ := exists_uniform_nlsWKB_diagonal_oscillatory_tail_bound_of_bounded_displacement s N hs hNs R D hR hD
  refine ⟨K,hK,C,hC,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD _hδM t
  exact h K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD t

end NLS.ZakharovShabat
