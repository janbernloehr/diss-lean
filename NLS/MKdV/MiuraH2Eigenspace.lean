import NLS.KdV.HillL2EigenspaceEquiv
import NLS.KdV.SingularDirichletMiuraEquation
import NLS.MKdV.MiuraHillSpectralIdentification

/-! # Actual Miura Hill/Dirac geometric eigenspace comparison

Both source spaces retain their full native operator domains. The Miura
potential is identified coefficient by coefficient before transporting the
entire eigenspace through the weak factorization and full H2 recovery.
-/
noncomputable section
open Complex NLS.KdV NLS.ZakharovShabat NLS.Fourier
open NLS.Fourier.SmoothPeriodicTest NLS.Fourier.PeriodicFourierLebesgue
namespace NLS.MKdV

theorem sobolevMiuraHillPotential_factorization (a : ScalarDomain 2) :
    sobolevMiuraHillPotential a = derivative (Coeff.periodDoubleSobolev a)+
      potentialMul (by norm_num) (Coeff.periodDouble (scalarInclusion a)) (Coeff.periodDoubleSobolev a) := by
  change Coeff.periodDouble ((2:ℂ) • derivative a+potentialMul (by norm_num) (scalarInclusion a) a) = _
  rw [map_add,← Coeff.derivative_periodDoubleSobolev,← potentialMul_periodDoubleSobolev]

theorem sobolevMiuraHillPotential_original (a : ScalarDomain 2) :
    hillL2HminusOne (sobolevMiuraWeightedPotential a) =
      singularHillMiuraPotential (Coeff.periodDouble (scalarInclusion a)) := by
  apply Subtype.ext
  apply Distribution.ext_coefficients
  intro n
  rw [hillL2HminusOne_coefficient,singularHillMiuraPotential_coefficient]
  have hq : (sobolevMiuraWeightedPotential a).val n = sobolevMiuraHillPotential a n := by
    simpa only [SpectralWeight.toCoeff_apply,SpectralWeight.one_apply,ofReal_one,div_one]
      using congrArg (fun q : Coeff 2 => q n) (toCoeff_sobolevMiuraWeightedPotential a)
  rw [hq,sobolevMiuraHillPotential_factorization]
  simp only [lp.coeFn_add,Pi.add_apply,ZakharovShabat.derivative_apply,potentialMul_apply,
    Coeff.periodDoubleSobolev_apply]

/-- The complete original H1 Dirac eigenspace and actual H2 Hill eigenspace
are linearly equivalent, for every complex H1 source and nonzero frequency. -/
def miuraH2EigenspaceEquiv (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    periodicEigenspace (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a))) z ≃ₗ[ℂ]
      hillSobolevEigenspace (sobolevMiuraHillPotential a) (z^2) := by
  have he := hillL2EigenspaceOriginalEquiv (sobolevMiuraWeightedPotential a) (z^2)
  rw [sobolevMiuraHillPotential_original,toCoeff_sobolevMiuraWeightedPotential] at he
  exact (diracMiuraHillEigenspaceEquiv (Coeff.periodDouble (scalarInclusion a)) z hz).trans he.symm

theorem finrank_miuraH2Eigenspace (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    Module.finrank ℂ (hillSobolevEigenspace (sobolevMiuraHillPotential a) (z^2)) =
      Module.finrank ℂ
        (periodicEigenspace (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a))) z) :=
  (miuraH2EigenspaceEquiv a z hz).finrank_eq.symm

theorem finiteDimensional_miuraH2Eigenspace (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0)
    (hzs : z ∈ periodicSpectrum (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a)))) :
    FiniteDimensional ℂ (hillSobolevEigenspace (sobolevMiuraHillPotential a) (z^2)) := by
  have : FiniteDimensional ℂ
      (periodicEigenspace (by norm_num) (periodOnePotential (sobolevSourceInclusion (a,a))) z) :=
    finiteDimensional_periodicEigenspace (by norm_num)
      (periodOnePotential (sobolevSourceInclusion (a,a))) z hzs
  exact FiniteDimensional.of_injective (miuraH2EigenspaceEquiv a z hz).symm.toLinearMap
    (miuraH2EigenspaceEquiv a z hz).symm.injective

end NLS.MKdV
