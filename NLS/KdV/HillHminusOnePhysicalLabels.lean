import NLS.KdV.HillHminusOnePhysicalSpectrum
import NLS.KdV.HillHminusOneCanonicalRealLabels

/-! # The canonical real labels enumerate the full original physical spectrum

Every characteristic label is now an actual eigenvalue on the original
H1 operator domain, and every physical spectral point is one of these
labels. The lowest label is physically minimal. Original real operator
root spaces are semisimple; equality of physical multiplicities with the
previous scalar analytic multiplicities is a separate statement.
-/
noncomputable section
set_option autoImplicit false
open Set Complex
open scoped ENNReal
namespace NLS.KdV
open NLS.Fourier NLS.Fourier.PeriodicFourierLebesgue

theorem hillHminusRealLabels_physical_spectrum_iff
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ) :
    z ∈ singularHillSpectrum (periodOneSingularPotential q) ↔
      ∃ j : ℕ, z = (hillHminusRealLabels q hr j : ℂ) := by
  rw [periodOneSingularHillSpectrum_iff_characteristic,hillHminusRealLabels_root_iff q hr]

theorem hillHminusRealLabels_physical_eigenvector
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (j : ℕ) :
    ∃ f : FourierLebesgueSpace (2 : ℝ) 1 2, f ≠ 0 ∧
      singularHillOperator (periodOneSingularPotential q) f =
        (hillHminusRealLabels q hr j : ℂ) • singularHillDomainInclusion f :=
  (hillHminusRadicand_zero_iff_original_H1_eigenvector q _).mp (hillHminusRealLabels_root q hr j)

theorem hillHminusLowestRealRoot_physical_minimal
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ)
    (hz : z ∈ singularHillSpectrum (periodOneSingularPotential q)) : hillHminusLowestRealRoot q hr ≤ z.re := by
  obtain ⟨j,rfl⟩ := (hillHminusRealLabels_physical_spectrum_iff q hr z).mp hz
  rw [ofReal_re,← hillHminusRealLabels_zero_eq_lowest q hr]
  exact monotone_hillHminusRealLabels q hr (Nat.zero_le j)

theorem hillHminusReal_original_root_spaces_semisimple
    (q : PeriodOneHminusOne) (hr : IsRealPeriodOneHminusOne q) (z : ℂ) :
    singularHillRootSpaceTop (periodOneSingularPotential q) z =
      singularHillRootSpace (periodOneSingularPotential q) z 1 :=
  singularHillRootSpaceTop_eq_one_of_real _ (periodOneSingularPotential_real q hr) z

end NLS.KdV
