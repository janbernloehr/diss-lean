import NLS.KdV.HillRiccatiMeanZeroLift
import NLS.Articles.KdVPseudomeasures.OriginalHillInverseActionTrace

/-! Mean-zero real Riccati lifts on the ENTIRE original distribution
domain, with the literal Fourier energy shift, original action labels,
and exact inverse-frequency action normalization retained. -/
noncomputable section
open Set Complex NLS.KdV NLS.ZakharovShabat
namespace NLS.Articles.KdVPseudomeasures

theorem exists_original_mean_zero_real_Miura_lift (q : OriginalHminusOnePotential) :
    ∃ u : PeriodOneRealL2, u.val 0=0 ∧
      periodOneMiura u.val=originalPeriodOneCoefficients q+
        periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)) := by
  obtain ⟨u,hu,hi⟩ := exists_mean_zero_real_Miura_lift (originalHillRealMeanZeroSource q)
  exact ⟨u,hu,by simpa only [originalHillRealMeanZeroSource_inclusion] using hi⟩

/-- The SAME mean-zero lift carries ALL actual original canonical actions
and their complete inverse-frequency sum; no exterior shift is needed. -/
theorem exists_original_mean_zero_Miura_action_lift (q : OriginalHminusOnePotential) :
    ∃ u : PeriodOneRealL2, u.val 0=0 ∧
      periodOneMiura u.val=originalPeriodOneCoefficients q+
        periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ)) ∧
      (∀ n : ℕ+, originalCanonicalHillAction n q=hillHminusMiuraIndexedAction u.val (n:ℕ)) ∧
      HasSum (fun n : ℕ+ => (hillHminusMiuraIndexedAction u.val (n:ℕ)).re/(Real.pi*(n:ℕ)))
        (‖hillRealSignedMap (originalHillRealMeanZeroSource q)‖^2/(2*Real.pi)) := by
  obtain ⟨u,hu,hi⟩ := exists_original_mean_zero_real_Miura_lift q
  have hI (n : ℕ+) : originalCanonicalHillAction n q=hillHminusMiuraIndexedAction u.val (n:ℕ) :=
    originalCanonicalHillAction_eq_Miura_all q u (‖u.val‖^2) hi n
  refine ⟨u,hu,hi,hI,?_⟩
  simpa only [hI] using hasSum_originalCanonicalHillAction_inverse q

/-- The removed energy of every such mean-zero lift is an ACTUAL original
periodic spectral point, including its possible zero-energy case. -/
theorem original_mean_zero_Miura_shift_mem_spectrum
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (hu : u.val 0=0)
    (hi : periodOneMiura u.val=originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 ((‖u.val‖^2:ℝ):ℂ))) :
    -((‖u.val‖^2:ℝ):ℂ) ∈ singularHillSpectrum q.val := by
  have hz := (hillMiura_zero_mem_spectrum_iff_mean_zero u).mpr hu
  have hd := (canonicalDiscriminant_sq_eq_four_iff
    (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _) 0).mpr hz
  have ht := hillHminusDiscriminant_shifted_miura_square (originalPeriodOneCoefficients q) u.val
    ((‖u.val‖^2:ℝ):ℂ) 0 hi
  simp only [zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_sub] at ht
  have hs : -((‖u.val‖^2:ℝ):ℂ) ∈ singularHillSpectrum (periodOneOriginal (originalPeriodOneCoefficients q)) := by
    apply (singularHillSpectrum_periodOne_iff_discriminant _ _).mpr
    rw [ht]
    exact hd
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hs

end NLS.Articles.KdVPseudomeasures
