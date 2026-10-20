import NLS.ZakharovShabat.SourceCriticalWeightedDisplacement
import NLS.ZakharovShabat.SourceCriticalMidpointHigherSobolev

/-! # Inverse-index displacement of periodic endpoints

Critical-point displacement, the critical-midpoint correction, and the original gap bound control both periodic endpoints on complex Sobolev neighborhoods.
-/

noncomputable section
open Set Complex
open scoped ENNReal
namespace NLS.ZakharovShabat

/-- Both actual periodic endpoints have a locally uniform inverse-index
displacement bound on the original Hs space near every real source.
The estimate includes central indices and collapsed gaps. -/
theorem exists_local_higherSobolev_periodic_weighted_displacement_bounds
    (s : ℕ) (hs : 1 ≤ s) (a₀ : realTypeHigherSobolevSourceLocus s) :
    ∃ U : Set (SobolevSource s), IsOpen U ∧ a₀.val ∈ U ∧
      ∃ R M : ℝ, 0 ≤ R ∧ 0 ≤ M ∧ ∀ ab ∈ U,
        ‖ab‖ ≤ R ∧ ∀ n : ℤ,
        (1+|(n:ℝ)|)*‖canonicalPeriodicLeft (by norm_num) (by norm_num)
          (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n-(Real.pi:ℂ)*n‖ ≤ M ∧
        (1+|(n:ℝ)|)*‖canonicalPeriodicRight (by norm_num) (by norm_num)
          (periodOnePotential (higherSobolevSourceInclusion s ab)) (periodOnePotential_mem _) n-(Real.pi:ℂ)*n‖ ≤ M := by
  obtain ⟨Uc,hUc,hac,R,_,M,hR,_,hM,hcritical⟩ :=
    exists_local_higherSobolev_critical_weighted_displacement_bounds s hs a₀
  obtain ⟨Um,hUm,ham,C,hC,hmid⟩ := exists_local_higherSobolev_critical_midpoint_bound s a₀
  obtain ⟨Ug,hUg,hag,G,hG,hgap⟩ := exists_local_sourceWeightedGapSequence_bound
    (by norm_num) (by norm_num) (SpectralWeight.sobolev s (Nat.cast_nonneg s))
    (higherSobolevSourceInclusion s) (higherSobolevSourceWeightedPeriodOne s)
    (weightedBaseToPair_higherSobolevSourceWeightedPeriodOne s) a₀.val
  refine ⟨Uc ∩ (Um ∩ Ug),hUc.inter (hUm.inter hUg),⟨hac,ham,hag⟩,
    R,M+C+G,hR,by positivity,?_⟩
  intro ab hab
  obtain ⟨habR,_,hc⟩ := hcritical ab hab.1
  obtain ⟨e,he,hen⟩ := hmid ab hab.2.1
  refine ⟨habR,?_⟩
  intro n
  let φ := periodOnePotential (higherSobolevSourceInclusion s ab)
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
    have h := (sourceHmWeightedGapSequence_majorant s ab n).trans
      ((lp.norm_apply_le_norm (by norm_num : (2:ℝ≥0∞) ≠ 0) _ n).trans (hgap ab hab.2.2))
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
