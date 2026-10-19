import NLS.ZakharovShabat.SobolevWKBLeadingLowerExpansion
import NLS.Fourier.PartialIntervalMassCorrectionSampling
import NLS.ZakharovShabat.WKBLeadingFrequencyCutoff
import NLS.SequenceSpaces.WeightedMultiplier

/-! # Sharp Sobolev tails for the WKB mass correction

The weighted mass correction gives an H^(N+1) tail under the displacement budgets, uniformly for every larger cutoff.
-/

noncomputable section
open Set Complex MeasureTheory NLS.Fourier
open scoped ContDiff ENNReal
namespace NLS.ZakharovShabat

/-- The explicit first mass correction to the leading forced response is
an H^(N+1) tail, uniformly on original Hs balls through N=s and over the
whole physical period. -/
theorem exists_uniform_nlsWKB_mass_correction_tail_bound
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
          (-I)*((2*I*z)⁻¹)^(N+1)*nlsWKBMassCorrectionIntegral a b (nlsRiccatiDensity a b N) z t
          else 0) ∧ ‖q‖ ≤ C := by
  classical
  obtain ⟨K,hK,hcut⟩ := exists_wkb_leading_frequency_cutoff D M hD
  obtain ⟨A,hA,hpot⟩ := exists_uniform_first_potential_pointwise_bound s hs R hR
  obtain ⟨L,hL,hL2⟩ := exists_uniform_nlsRiccatiDensity_L2_bound s N hNs R hR
  refine ⟨K,hK,2*A^2*Real.exp (3*D)*L,by positivity,?_⟩
  intro K' hK' ab hab a b ha hb hpa hpb hca hcb δ hδD hδM t
  let ρ := nlsRiccatiDensity a b N
  let P := nlsWKBMassPrimitive a b
  have hρ : Continuous ρ := (contDiff_nlsRiccatiDensity a b ha hb N).continuous
  have hρL2 := memLp_two_interval hρ 0 1 (by norm_num : (0:ℝ) ≤ 1)
  have hP : Continuous P := continuous_nlsWKBMassPrimitive a b ha.continuous hb.continuous
  have hPn (x : ℝ) (hx : x ∈ Icc (0:ℝ) 1) : ‖P x‖ ≤ A^2 :=
    norm_nlsWKBMassPrimitive_le a b A hA
      (hpot ab hab a b ha hb hpa hpb hca hcb)
      (hpot (ab.2,ab.1) (by simpa only [Prod.norm_def,max_comm] using hab)
        b a hb ha hpb hpa hcb hca) x hx
  have hρn : ‖unitIntervalMemLpCoefficients ρ hρL2‖ ≤ L := by
    have he := norm_sq_unitIntervalMemLpCoefficients ρ hρL2
    have he' : ‖unitIntervalMemLpCoefficients ρ hρL2‖ =
        Real.sqrt (∫ x in (0:ℝ)..1, ‖ρ x‖^2) := by
      rw [← he,Real.sqrt_sq (norm_nonneg _)]
    rw [he']
    exact hL2 ab hab a b ha hb hpa hpb hca hcb
  obtain ⟨q,hq,hqn⟩ := exists_partial_interval_massCorrection_lattice_coefficients
    ρ P hρL2 hP (A^2) (sq_nonneg _) hPn δ t t.property
  have hqbound : ‖q‖ ≤ 2*A^2*Real.exp (3*D)*L := by
    apply hqn.trans
    apply mul_le_mul _ hρn (norm_nonneg _) (by positivity)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
  let ν (n : ℤ) := (Real.pi:ℂ)*n+δ n
  let m (n : ℤ) := if K' ≤ n.natAbs then (-I)*((2*I*ν n)⁻¹)^(N+1) else 0
  let v := Weight.sobolev ((N+1:ℕ):ℝ)
  have hδ (n : ℤ) : ‖δ n‖ ≤ D := (lp.norm_apply_le_norm (by simp) δ n).trans hδD
  have hm (n : ℤ) : v n*‖m n‖ ≤ 1*Weight.one n := by
    by_cases hn : K' ≤ n.natAbs
    · have hh := (hcut δ hδ hδM n (hK'.trans hn)).2
      change 1+|(n:ℝ)| ≤ ‖ν n‖ at hh
      have hw : (1+|(n:ℝ)|)*‖(2*I*ν n)⁻¹‖ ≤ 1 := by
        simp only [norm_inv,norm_mul,norm_ofNat,norm_I,mul_one]
        rw [← div_eq_mul_inv]
        have hpos : (0:ℝ) < 1+|(n:ℝ)| := by positivity
        apply (div_le_one (by linarith : 0 < 2*‖ν n‖)).mpr
        linarith [norm_nonneg (ν n)]
      have hp := pow_le_pow_left₀ (by positivity) hw (N+1)
      simpa only [v,Weight.sobolev_apply,Real.rpow_natCast,m,if_pos hn,
        norm_mul,norm_neg,norm_I,one_mul,norm_pow,Weight.one_apply,mul_pow,one_pow] using hp
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
    · simp only [m,if_pos hn,ν,nlsWKBMassCorrectionIntegral,ρ,P]
    · simp [m,hn]
  · have hn := WeightedCoeff.norm_weightedMultiplier_le Weight.one v m 1 zero_le_one hm q₀
    simpa only [one_mul,LinearIsometryEquiv.norm_map] using hn.trans (by
      simpa only [one_mul,LinearIsometryEquiv.norm_map,q₀] using hqbound)

end NLS.ZakharovShabat
