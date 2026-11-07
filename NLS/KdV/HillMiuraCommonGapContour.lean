import NLS.KdV.HillMiuraEnergyGapCoordinates
import NLS.ComplexAnalysis.ThinIntervalContour
import NLS.ZakharovShabat.SourcePositivePeriodCircle

/-! ANY TWO real shifted Miura representations of the same original
potential admit a common genuine energy comparison contour at EVERY
positive original gap. It lies in both local square-root disk domains
and winds once about EVERY point of the same original closed gap.
The contour is selected before any numerator index. -/
noncomputable section
open Set Metric Complex NLS.ZakharovShabat NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.KdV

theorem exists_common_hillMiura_gap_contour (q : PeriodOneHminusOne) (hq : IsRealPeriodOneHminusOne q)
    (u v : PeriodOneRealL2) (c d : ℝ)
    (hu : periodOneMiura u.val = q+periodOneL2Inclusion (lp.single 2 0 (c:ℂ)))
    (hv : periodOneMiura v.val = q+periodOneL2Inclusion (lp.single 2 0 (d:ℂ)))
    (hc : -(c:ℂ) ∉ singularHillSpectrum (periodOneOriginal q))
    (hd : -(d:ℂ) ∉ singularHillSpectrum (periodOneOriginal q)) (m : ℕ+) :
    ∃ A : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal u.val) ((m:ℕ):ℤ),
    ∃ B : SourceCriticalRootPeriodCircle (by norm_num) (by norm_num) (hillMiuraDiagonal v.val) ((m:ℕ):ℤ),
      0 < A.center-A.radius ∧ 0 < B.center-B.radius ∧
      ∃ Γ : PiecewiseC1Loop,
        Γ.Inside ((energyFrequencyDisk (c:ℂ) (A.center:ℂ) A.radius ∩
          energyFrequencyDisk (d:ℂ) (B.center:ℂ) B.radius) \
            Complex.ofReal '' Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ)))) ∧
        ∀ E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))),
          Γ.windingIntegral (E:ℂ) = 1 := by
  obtain ⟨A,hA⟩ := exists_positive_sourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
    (hillMiuraDiagonal u.val) (hillMiuraRealSource u).property ((m:ℕ):ℤ)
    (hillMiura_positive_gap_left_pos u ((m:ℕ):ℤ) (by exact_mod_cast m.pos))
  obtain ⟨B,hB⟩ := exists_positive_sourceCriticalRootPeriodCircle (by norm_num) (by norm_num)
    (hillMiuraDiagonal v.val) (hillMiuraRealSource v).property ((m:ℕ):ℤ)
    (hillMiura_positive_gap_left_pos v ((m:ℕ):ℤ) (by exact_mod_cast m.pos))
  let U := energyFrequencyDisk (c:ℂ) (A.center:ℂ) A.radius ∩ energyFrequencyDisk (d:ℂ) (B.center:ℂ) B.radius
  have hU : IsOpen U := (energyFrequencyDisk_open _ _ _).inter (energyFrequencyDisk_open _ _ _)
  have hI : ∀ E ∈ Icc (hillHminusLabels q hq (2*(m:ℕ)-1)) (hillHminusLabels q hq (2*(m:ℕ))), (E:ℂ) ∈ U := by
    intro E hE
    have hEu := hillMiura_frequency_of_original_gap q hq u c hu hc m E hE
    have hEv := hillMiura_frequency_of_original_gap q hq v d hv hd m E hE
    exact ⟨⟨hEu.1,A.gap hEu.2.1⟩,⟨hEv.1,B.gap hEv.2.1⟩⟩
  obtain ⟨Γ,hΓ,hw⟩ := exists_thin_interval_contour _ _
    (monotone_hillHminusLabels q hq (by omega)) U hU hI
  exact ⟨A,B,hA,hB,Γ,hΓ,hw⟩

end NLS.KdV
