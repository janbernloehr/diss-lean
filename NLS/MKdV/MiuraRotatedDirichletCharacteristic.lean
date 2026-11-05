import NLS.MKdV.MiuraHillDirichletComparison
import NLS.MKdV.MiuraDiscriminantCotangent
import NLS.ZakharovShabat.ContinuousSourceAntiDiscriminantGradient
import NLS.ZakharovShabat.SourcePhaseCompatibility

/-! # Exact characteristic normalization at the original rotated source

This compares independent physical IVPs, rather than defining the scalar
characteristic by source spectral data. The equality includes z=0 and
all original complex H¹ potentials.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.LinearVolterra NLS.Fourier NLS.ZakharovShabat NLS.KdV
open scoped ENNReal
namespace NLS.MKdV

theorem miura_rotated_Dirichlet_characteristic (a : ScalarDomain 2) (z : ℂ) :
    z*hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2) =
      periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
        (sourcePhase (sobolevSourceInclusion (a,a))) z := by
  rw [hillL2DirichletCharacteristic_miura]
  have h := quasiHillDirichletCharacteristic_eq_rotatedZS (periodOneMiuraCurve a)
    (miuraDiagonalCurveCLM (periodOneMiuraCurve a)) (by intro t;rfl) z
  apply h.trans
  exact (periodOneBoundaryCharacteristic_eq_classical_of_continuous .dirichlet
    (sourcePhase (sobolevSourceInclusion (a,a))) _
    (physicalBase_sourcePhase_compatibility _ _ (physicalBase_miuraDiagonal a)) z).symm

theorem miura_rotated_Dirichlet_characteristic_odd (a : ScalarDomain 2) (z : ℂ) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
        (sourcePhase (sobolevSourceInclusion (a,a))) (-z) =
      -periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
        (sourcePhase (sobolevSourceInclusion (a,a))) z := by
  rw [← miura_rotated_Dirichlet_characteristic a (-z),← miura_rotated_Dirichlet_characteristic a z,neg_sq]
  ring

theorem miura_rotated_Dirichlet_characteristic_zero (a : ScalarDomain 2) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a))) 0 = 0 := by
  rw [← miura_rotated_Dirichlet_characteristic a 0,zero_mul]

theorem miura_rotated_Dirichlet_zero_iff (a : ScalarDomain 2) (z : ℂ) (hz : z ≠ 0) :
    periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a))) z = 0 ↔
        hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2) = 0 := by
  rw [← miura_rotated_Dirichlet_characteristic,mul_eq_zero,or_iff_right hz]

end NLS.MKdV
