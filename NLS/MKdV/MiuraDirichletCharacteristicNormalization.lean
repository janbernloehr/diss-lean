import NLS.MKdV.MiuraDirichletRootIdentification
import NLS.ComplexAnalysis.SquaredCharacteristicLimit

/-! # Original characteristic derivative normalization under Miura squaring

At a positive divisor frequency, the actual source characteristic derivative
is twice the scalar Dirichlet energy times the actual scalar derivative.
The exceptional source zero has derivative equal to the scalar value at zero.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem deriv_miura_rotated_Dirichlet_characteristic (a : ScalarDomain 2) (z : ℂ) :
    deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a)))) z =
      hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2)+
        2*z^2*deriv (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)) (z^2) := by
  exact NLS.ComplexAnalysis.deriv_of_squared_characteristic _ _
    (fun w => (miura_rotated_Dirichlet_characteristic a w).symm) z
    (analyticOnNhd_hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
      (z^2) (mem_univ _)).differentiableAt

theorem deriv_miura_rotated_Dirichlet_characteristic_at_root (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (n : ℕ) (hn : 1 ≤ n) :
    let q := realSobolevMiuraHillPotential a ha
    let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a)))) (miuraRotatedDirichletRoots a n) =
        2*E*deriv (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)) E := by
  dsimp only
  rw [deriv_miura_rotated_Dirichlet_characteristic,miuraRotatedDirichletRoots_sq a ha n hn,
    ← realSobolevMiuraHillPotential_toCoeff a ha,
    hillDirichletEnergy_zero,zero_add]

theorem hillL2DirichletCharacteristic_miura_zero_ne_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) 0 ≠ 0 := by
  have hn := deriv_periodOneBoundaryCharacteristic_at_canonicalRoot_ne_zero_of_realType
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num) .dirichlet
    (sourcePhase (sobolevSourceInclusion (a,a)))
    (isRealType_sourcePhase _ (realDiagonalH1Source a ha).property) 0
  change deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
    (sourcePhase (sobolevSourceInclusion (a,a)))) (miuraRotatedDirichletRoots a 0) ≠ 0 at hn
  simpa only [miuraRotatedDirichletRoots_zero a ha,deriv_miura_rotated_Dirichlet_characteristic,
    zero_pow (by norm_num : 2 ≠ 0),mul_zero,zero_mul,add_zero] using hn

end NLS.MKdV
