import NLS.ZakharovShabat.SourceSpectralDisplacementSobolevBall
import NLS.ZakharovShabat.SourceCriticalMidpointSobolevBall

/-! # Uniform periodic endpoint displacements

Both periodic endpoints have common inverse-index displacement bounds throughout each real Sobolev ball, including all central indices.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both periodic endpoints have a common inverse-index displacement
bound on every entire real original Hs ball, including the central indices. -/
theorem exists_uniform_real_higherSobolev_periodic_displacement_bound
    (s : ℕ) (hs : 1 ≤ s) (R : ℝ) (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ab : realTypeHigherSobolevSourceLocus s, ‖ab.val‖ ≤ R → ∀ n : ℤ,
      (1+|(n:ℝ)|)*‖canonicalPeriodicLeft (by norm_num) (by norm_num)
        (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n-(Real.pi:ℂ)*n‖ ≤ M ∧
      (1+|(n:ℝ)|)*‖canonicalPeriodicRight (by norm_num) (by norm_num)
        (periodOnePotential (higherSobolevSourceInclusion s ab.val)) (periodOnePotential_mem _) n-(Real.pi:ℂ)*n‖ ≤ M := by
  obtain ⟨_,M,_,hM,hcritical⟩ := exists_uniform_real_higherSobolev_displacement_envelopes s hs R hR
  obtain ⟨C,hC,hmid⟩ := exists_uniform_real_higherSobolev_critical_midpoint_bound s hs R
  obtain ⟨G,hG,hgap⟩ := exists_sourceHmWeightedGapSequence_bound_on_physical_ball s hs
    (2*(2*Real.pi)^s*R)
  refine ⟨M+C+G,by positivity,?_⟩
  intro ab hab
  have hc := (hcritical ab hab).2.2
  obtain ⟨e,he,hen⟩ := hmid ab hab
  have hgap' : ‖sourceHmWeightedGapSequence s ab.val‖ ≤ G := hgap ab
    ((norm_sourcePiSobolevCoordinates_le_native s s le_rfl ab.val).trans (by gcongr))
  intro n
  let φ := periodOnePotential (higherSobolevSourceInclusion s ab.val)
  let κ := canonicalCriticalPoints (by norm_num) (by norm_num) φ (periodOnePotential_mem _) n
  let τ := canonicalPeriodicMidpoint (by norm_num) (by norm_num) φ (periodOnePotential_mem _) n
  let g := canonicalPeriodicGap (by norm_num) (by norm_num) φ (periodOnePotential_mem _) n
  let w : ℝ := 1+|(n:ℝ)|
  have hw : 1 ≤ w := by dsimp [w]; linarith [abs_nonneg (n:ℝ)]
  have hκ : w*‖κ-(Real.pi:ℂ)*n‖ ≤ M := by
    simpa only [w,κ,φ,sourceCriticalDisplacement,canonicalCriticalDisplacement_apply] using hc n
  have hpow : w ≤ w^(2*s) := by
    simpa only [pow_one] using pow_le_pow_right₀ hw (by omega : 1 ≤ 2*s)
  have hem : w*‖κ-τ‖ ≤ C := by
    have h := (le_div_iff₀ ((Weight.sobolev ((2*s:ℕ):ℝ)).positive n)).mp (WeightedCoeff.norm_apply_le _ _ e n)
    simp only [Weight.sobolev_apply,Real.rpow_natCast,he n] at h
    change ‖κ-τ‖*w^(2*s) ≤ ‖e‖ at h
    calc
      _ ≤ w^(2*s)*‖κ-τ‖ := mul_le_mul_of_nonneg_right hpow (norm_nonneg _)
      _ ≤ ‖e‖ := by simpa only [mul_comm] using h
      _ ≤ C := hen
  have hgp : w^s*‖g‖ ≤ G := by
    have h := (sourceHmWeightedGapSequence_majorant s ab.val n).trans
      ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ n).trans hgap')
    simpa only [sourcePeriodicGapDisplacement_apply] using h
  have hg : w*‖g‖ ≤ G :=
    (mul_le_mul_of_nonneg_right (by simpa only [pow_one] using pow_le_pow_right₀ hw hs)
      (norm_nonneg g)).trans hgp
  have ha : canonicalPeriodicLeft (by norm_num) (by norm_num) φ (periodOnePotential_mem _) n-(Real.pi:ℂ)*n =
      (κ-(Real.pi:ℂ)*n)-(κ-τ)-g/2 := by dsimp [τ,g,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have hb : canonicalPeriodicRight (by norm_num) (by norm_num) φ (periodOnePotential_mem _) n-(Real.pi:ℂ)*n =
      (κ-(Real.pi:ℂ)*n)-(κ-τ)+g/2 := by dsimp [τ,g,canonicalPeriodicMidpoint,canonicalPeriodicGap]; ring
  have ht := norm_sub_le (κ-(Real.pi:ℂ)*n) (κ-τ)
  constructor
  · rw [ha]
    have h := norm_sub_le ((κ-(Real.pi:ℂ)*n)-(κ-τ)) (g/2)
    rw [norm_div,norm_ofNat] at h
    have hbound := mul_le_mul_of_nonneg_left (h.trans (add_le_add ht le_rfl)) (zero_le_one.trans hw)
    nlinarith
  · rw [hb]
    have h := norm_add_le ((κ-(Real.pi:ℂ)*n)-(κ-τ)) (g/2)
    rw [norm_div,norm_ofNat] at h
    have hbound := mul_le_mul_of_nonneg_left (h.trans (add_le_add ht le_rfl)) (zero_le_one.trans hw)
    nlinarith

end NLS.ZakharovShabat
