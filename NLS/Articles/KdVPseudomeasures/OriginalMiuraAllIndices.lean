import NLS.Articles.KdVPseudomeasures.OriginalHillLabels
import NLS.KdV.HillHminusOneMiuraOutsideShift
import NLS.KdV.HillHminusOneMiuraCanonicalGaps

/-! # All original physical Hill indices under a rough Miura representation

The entire original real mean-zero period-one H-minus-one distribution
is retained. Every original Hill label, including all low repetitions and
the bottom endpoint, has the exact squared Dirac index. Miura action zero
detection consequently uses the original canonical gap at EVERY positive
index. Independence of the Miura action from the chosen lift and shift
is still a separate obligation before defining a global canonical action.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
namespace NLS.Articles.KdVPseudomeasures
open NLS.KdV

theorem originalHillLabels_eq_squared_miuraDirac
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum q.val) :
    originalHillLabels q = hillMiuraSquaredLabels u.val c := by
  apply hillHminusLabels_eq_squared_miuraDirac
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) u c himage
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hc

theorem originalCanonicalGapValues_eq_miuraDirac_product
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum q.val) (n : ℕ+) :
    originalCanonicalGapValues q (n : ℕ) =
      (hillMiuraDiracRight u.val (n : ℕ)-hillMiuraDiracLeft u.val (n : ℕ))*
        (hillMiuraDiracRight u.val (n : ℕ)+hillMiuraDiracLeft u.val (n : ℕ)) := by
  have hout : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal (originalPeriodOneCoefficients q)) := by
    simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hc
  have h := hillHminus_gap_eq_miuraDirac_product (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) u c himage hout (n : ℕ) n.pos
  have hn : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simpa only [originalCanonicalGapValues,if_neg hn,Int.natAbs_natCast,originalHillLabels] using h

theorem originalMiuraAction_eq_zero_iff_canonicalGap
    (q : OriginalHminusOnePotential) (u : PeriodOneRealL2) (c : ℝ)
    (himage : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 (c : ℂ)))
    (hc : -(c : ℂ) ∉ singularHillSpectrum q.val) (n : ℕ+) :
    hillHminusMiuraIndexedAction u.val (n : ℕ) = 0 ↔ originalCanonicalGapValues q (n : ℕ) = 0 := by
  have hout : -(c : ℂ) ∉ singularHillSpectrum (periodOneOriginal (originalPeriodOneCoefficients q)) := by
    simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hc
  have h := hillHminusMiuraIndexedAction_eq_zero_iff_Hill_gap (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) u c himage hout (n : ℕ) n.pos
  have hn : ((n : ℕ) : ℤ) ≠ 0 := by exact_mod_cast n.ne_zero
  simpa only [originalCanonicalGapValues,if_neg hn,Int.natAbs_natCast,originalHillLabels] using h

theorem originalHillLabels_bottom_lt_first (q : OriginalHminusOnePotential) :
    originalHillLabels q 0 < originalHillLabels q 1 := by
  obtain ⟨c,_,_,u,himage,hc⟩ := exists_real_periodOneMiura_shift_outside_spectrum
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) 0
  apply hillHminusLabels_bottom_lt_first (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) u (c^2)
  · simpa only [ofReal_pow] using himage
  · simpa only [ofReal_pow] using hc

theorem originalHillLabels_bottom_multiplicity_one (q : OriginalHminusOnePotential) :
    singularHillAlgebraicMultiplicity q.val (originalHillLabels q 0 : ℂ) = 1 := by
  obtain ⟨c,_,_,u,himage,hc⟩ := exists_real_periodOneMiura_shift_outside_spectrum
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) 0
  have h := hillHminusLabels_bottom_multiplicity_one (originalPeriodOneCoefficients q)
    (originalPeriodOneCoefficients_real q) u (c^2)
    (by simpa only [ofReal_pow] using himage) (by simpa only [ofReal_pow] using hc)
  change analyticOrderNatAt (fun E => hillHminusDiscriminant (originalPeriodOneCoefficients q) E^2-4)
    (originalHillLabels q 0 : ℂ) = 1 at h
  rw [analyticOrderNatAt_hillHminusDiscriminant_eq_physicalMultiplicity
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q)] at h
  simpa only [periodOneOriginal_originalPeriodOneCoefficients] using h

theorem exists_originalMiura_all_index_representation
    (q : OriginalHminusOnePotential) (A : ℝ) :
    ∃ c : ℝ, 0 < c ∧ A < c ∧ ∃ u : PeriodOneRealL2,
      periodOneMiura u.val = originalPeriodOneCoefficients q+
        periodOneL2Inclusion (lp.single 2 0 ((c : ℂ)^2)) ∧
      -((c : ℂ)^2) ∉ singularHillSpectrum q.val ∧
      originalHillLabels q = hillMiuraSquaredLabels u.val (c^2) ∧
      ∀ n : ℕ+, 0 ≤ (hillHminusMiuraIndexedAction u.val (n : ℕ)).re ∧
        (hillHminusMiuraIndexedAction u.val (n : ℕ)).im = 0 ∧
        (hillHminusMiuraIndexedAction u.val (n : ℕ) = 0 ↔ originalCanonicalGapValues q (n : ℕ) = 0) := by
  obtain ⟨c,hc,hAc,u,himage,hout⟩ := exists_real_periodOneMiura_shift_outside_spectrum
    (originalPeriodOneCoefficients q) (originalPeriodOneCoefficients_real q) A
  have hout' : -((c : ℂ)^2) ∉ singularHillSpectrum q.val := by
    simpa only [periodOneOriginal_originalPeriodOneCoefficients] using hout
  have himage' : periodOneMiura u.val = originalPeriodOneCoefficients q+
      periodOneL2Inclusion (lp.single 2 0 ((c^2 : ℝ) : ℂ)) := by
    simpa only [ofReal_pow] using himage
  have hc' : -((c^2 : ℝ) : ℂ) ∉ singularHillSpectrum q.val := by
    simpa only [ofReal_pow] using hout'
  refine ⟨c,hc,hAc,u,himage,hout',originalHillLabels_eq_squared_miuraDirac q u (c^2) himage' hc',?_⟩
  intro n
  have hs := hillHminusMiuraIndexedAction_positive_index_spec u (n : ℕ) (by exact_mod_cast n.pos)
  exact ⟨hs.1,hs.2.1,originalMiuraAction_eq_zero_iff_canonicalGap q u (c^2) himage' hc' n⟩

end NLS.Articles.KdVPseudomeasures
