import NLS.ZakharovShabat.SourceM1SpectralGeometry
import NLS.ZakharovShabat.SourceH1GapProductReduction

/-! # Quantitative gap factors for all M₁ weights on real sources -/
noncomputable section
namespace NLS.ZakharovShabat

/-- The exterior finite product retains 128 for every M₁ weight. -/
theorem sourceM1_real_exterior_product_le_128 (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (s : Finset ℤ) (n : ℤ) (hs : n ∉ s)
    (hsext : ∀ m ∈ s, N ≤ m.natAbs) (hn : N ≤ n.natAbs)
    (z : ℂ) (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n) :
    ‖∏ m ∈ s, (canonicalCriticalPoints (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m-z)/
      sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤ 128 := by
  have heven : weightedBaseToPair w φ ∈ pairParitySubspace 0 := hφ ▸ periodOnePotential_mem ψ.val
  have hG := M1_canonicalGap_finite_exterior_sq_le_three w hw φ heven N hN s hsext
  simp only [hφ] at hG
  apply le_trans (norm_finite_product_le_exp_sqrt_budgets s _
    (fun m => ‖canonicalPeriodicGap (by simp) (by norm_num)
      (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m‖)
    (fun m => 1/|((m-n:ℤ):ℝ)|) 3 (7/2) _ hG
    (ReciprocalSeries.sum_shifted_reciprocal_sq_le s n)) exterior_product_exponential_budget
  intro m hms
  have hmn : m ≠ n := fun he => hs (he ▸ hms)
  have hloc := sourceM1_endpoints_localization w hw ψ.val φ hφ m
    (exterior_index_localization_threshold ‖φ‖ N hN m (hsext m hms))
  have hzloc := sourceM1_gap_point_localization w hw ψ.val φ hφ n
    (exterior_index_localization_threshold ‖φ‖ N hN n hn) z hz
  have hcrit := sourceCanonicalCriticalPoint_mem_periodicSegment_of_realType
    (by simp) (by norm_num) m ψ.val ψ.property
  have hoff := gap_segment_midpoint_dist_le _ _ _ hcrit
  have hfactor := source_exterior_critical_factor_le (by simp) (by norm_num)
    ψ.val m n z hmn hloc.1 hloc.2 hzloc (hoff.trans (by
      change ‖canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m‖/2 ≤ _
      linarith [norm_nonneg (canonicalPeriodicGap (by simp) (by norm_num)
        (periodOnePotential ψ.val) (periodOnePotential_mem ψ.val) m)]))
  simpa only [one_div,div_eq_mul_inv,one_mul] using hfactor

/-- The squared central-product estimate is independent of upper weight growth. -/
theorem sourceM1_real_central_product_sq_le (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hNpos : 1 ≤ N) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ))
    (n : ℤ) (hn : N ≤ n.natAbs) (z : ℂ)
    (hz : z ∈ sourcePeriodicSegment (by simp) (by norm_num) ψ.val n) :
    ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
      (canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val)
        (periodOnePotential_mem ψ.val) m-z)/sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖^2 ≤
      8*((N:ℝ)+1) := by
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hNpos
  have hb (m : ℤ) (hm : m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ)) :=
    sourceM1_central_endpoints w hw ψ.val φ hφ N hN m (by simp only [Finset.mem_Ioo] at hm; omega)
  have hloc := sourceM1_gap_point_localization w hw ψ.val φ hφ n
    (exterior_index_localization_threshold ‖φ‖ N hN n hn) z hz
  have hlow := localized_point_abs_re_lower z n hloc
  have hn' : (N:ℝ) ≤ |(n:ℝ)| := by
    have h : (N:ℝ) ≤ (n.natAbs:ℝ) := by exact_mod_cast hn
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have hx : Real.pi*((N:ℝ)-1/5) ≤ |z.re| := by
    nlinarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hn')]
  have h := sourceReal_finite_gap_product_sq_le (by simp) (by norm_num) ψ.val ψ.property
    (Finset.Ioo (-(N:ℤ)) (N:ℤ)) (((N:ℝ)-1/2)*Real.pi)
    (mul_nonneg (by linarith) Real.pi_pos.le) hb z
    (sourcePeriodicSegment_im_eq_zero_of_realType (by simp) (by norm_num) ψ.val ψ.property n z hz)
    (by nlinarith [Real.pi_pos])
  exact h.trans (central_enclosing_ratio_le_eight N |z.re| hN1 hx)

/-- The closed-gap scalar estimate uses the original weighted norm and cutoff. -/
theorem sourceM1_real_gapFactor_le_2048_at_cutoff (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (hcut : (N:ℝ) ≤ 8*‖φ‖^2)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖sourceRealGapFactor (by simp) (by norm_num) ψ.val ψ.property n‖ ≤ 2048*(1+‖φ‖^2) := by
  apply (sourceRealGapFactor_norm_le_iff (by simp) (by norm_num)
    ψ.val ψ.property n (2048*(1+‖φ‖^2)) (by positivity)).mpr
  intro z hz
  have hdom := sourceStandardRootGapSegment_subset_omittedDomain_of_realType
    (by simp) (by norm_num) ψ.val ψ.property n
  rw [sourceStandardRoot_gapSegment_eq_periodicSegment] at hdom
  have hlim := sourceCriticalRootRatioExtension_le_finite_core (by simp) (by norm_num)
    ψ.val n N hn z (hdom hz) 128
    (fun s hs hsext => sourceM1_real_exterior_product_le_128 w hw ψ φ hφ N hN s n hs hsext hn z hz)
  by_cases hzero : N = 0
  · subst N
    simp only [Nat.cast_zero,neg_zero,Finset.Ioo_self,Finset.prod_empty,norm_one,mul_one] at hlim
    exact hlim.trans (by nlinarith [sq_nonneg ‖φ‖])
  have hcore := sourceM1_real_central_product_sq_le w hw ψ φ hφ N
    (Nat.one_le_iff_ne_zero.mpr hzero) hN n hn z hz
  have hnorm : ‖∏ m ∈ Finset.Ioo (-(N:ℤ)) (N:ℤ),
      (canonicalCriticalPoints (by simp) (by norm_num) (periodOnePotential ψ.val)
        (periodOnePotential_mem ψ.val) m-z)/sourceStandardRoot (by simp) (by norm_num) ψ.val m z‖ ≤
      16*(1+‖φ‖^2) := by nlinarith [sq_nonneg (‖φ‖^2),sq_nonneg ‖φ‖]
  linarith

/-- The action-gap estimate at a norm-adapted cutoff for an arbitrary M₁ weight. -/
theorem sourceM1_real_action_le_1536_at_cutoff (w : SpectralWeight) (hw : w.HasLinearFactor)
    (ψ : realTypeSourceSubmodule 2) (φ : WeightedCoeffPair w.toWeight 2)
    (hφ : weightedBaseToPair w φ = periodOnePotential ψ.val)
    (N : ℕ) (hN : 8*‖φ‖^2 ≤ 1+(N:ℝ)) (hcut : (N:ℝ) ≤ 8*‖φ‖^2)
    (n : ℤ) (hn : N ≤ n.natAbs) :
    ‖sourceComplexAction (by simp) (by norm_num) n ψ.val‖ ≤
      1536*(1+‖φ‖^2)*‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖^2 := by
  have h := sourceComplexAction_le_three_gapFactor_mul_gap_sq (by simp) (by norm_num) ψ.val ψ.property n
  have hfactor := sourceM1_real_gapFactor_le_2048_at_cutoff w hw ψ φ hφ N hN hcut n hn
  have hmul := mul_le_mul_of_nonneg_right hfactor
    (sq_nonneg ‖sourcePeriodicGapDisplacement (by simp) (by norm_num) ψ.val n‖)
  nlinarith

end NLS.ZakharovShabat
