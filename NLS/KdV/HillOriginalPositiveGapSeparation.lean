import NLS.KdV.HillMiuraEnergyGapCoordinates
import NLS.KdV.HillHminusOneMiuraOutsideShift

/-! Distinct ORIGINAL positive real Hill gaps are disjoint, including
collapsed gaps. This follows at EVERY index from strict real Dirac gap
separation and the proved common square-root energy correspondence. -/
noncomputable section
open Set Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal
namespace NLS.KdV

theorem hillMiura_original_positive_gaps_disjoint
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (u : PeriodOneRealL2) (c : ℝ)
    (hi : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (i j : ℕ+) (hij : i ≠ j) :
    Disjoint (Icc (hillHminusLabels q hq (2*(i:ℕ)-1)) (hillHminusLabels q hq (2*(i:ℕ))))
      (Icc (hillHminusLabels q hq (2*(j:ℕ)-1)) (hillHminusLabels q hq (2*(j:ℕ)))) := by
  apply Set.disjoint_left.mpr
  intro E hEi hEj
  have hfi := hillMiura_frequency_of_original_gap q hq u c hi hc i E hEi
  have hfj := hillMiura_frequency_of_original_gap q hq u c hi hc j E hEj
  have hI := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) ((i:ℕ):ℤ) _ hfi.2.1
  have hJ := sourcePeriodicSegment_re_mem_Icc (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) ((j:ℕ):ℤ) _ hfj.2.1
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hs := canonicalPeriodicRight_re_lt_left_of_lt (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property)
      (show ((i:ℕ):ℤ) < ((j:ℕ):ℤ) by exact_mod_cast hij)
    exact (not_lt_of_ge (hJ.1.trans hI.2)) hs
  · have hs := canonicalPeriodicRight_re_lt_left_of_lt (by norm_num) (by norm_num)
      (periodOnePotential (hillMiuraDiagonal u.val)) (periodOnePotential_mem _)
      (isRealType_periodOnePotential _ (hillMiuraRealSource u).property)
      (show ((j:ℕ):ℤ) < ((i:ℕ):ℤ) by exact_mod_cast hji)
    exact (not_lt_of_ge (hI.1.trans hJ.2)) hs

theorem hillHminusOriginal_positive_gaps_disjoint
    (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q) (i j : ℕ+) (hij : i ≠ j) :
    Disjoint (Icc (hillHminusLabels q hq (2*(i:ℕ)-1)) (hillHminusLabels q hq (2*(i:ℕ))))
      (Icc (hillHminusLabels q hq (2*(j:ℕ)-1)) (hillHminusLabels q hq (2*(j:ℕ)))) := by
  obtain ⟨d,_,_,u,hi,hc⟩ := exists_real_periodOneMiura_shift_outside_spectrum q hq 0
  have hi' : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 ((d^2:ℝ):ℂ)) := by
    simpa only [Complex.ofReal_pow] using hi
  have hc' : -((d^2:ℝ):ℂ) ∉ singularHillSpectrum (periodOneOriginal q) := by
    simpa only [Complex.ofReal_pow] using hc
  exact hillMiura_original_positive_gaps_disjoint q hq u (d^2) hi' hc' i j hij

end NLS.KdV
