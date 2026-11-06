import NLS.MKdV.MiuraDirichletEntireProduct
import NLS.MKdV.MiuraDirichletCharacteristicNormalization

/-! # The original independent divisor characteristic and its entire product

These identify the scalar IVP characteristic, its fixed signed source
labels and its original derivative normalization. The proofs include
infinite support, closed gaps, arbitrary signed mean and zero energy.
They supply the actual characteristic needed for Abelian interpolation;
the final canonical angle rotation remains a separate proof obligation.
-/
noncomputable section
open Set Complex Filter Topology
open NLS.MKdV NLS.KdV NLS.ZakharovShabat
open scoped ENNReal ComplexConjugate
namespace NLS.Articles.MKdVNLSHierarchies

theorem independent_Dirichlet_characteristic_original_complex_domain
    (a : ScalarDomain 2) (z : ℂ) :
    z*hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2) =
      periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
        (sourcePhase (sobolevSourceInclusion (a,a))) z :=
  miura_rotated_Dirichlet_characteristic a z

theorem independent_Dirichlet_divisor_original_indices
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (hn : 1 ≤ n) :
    (miuraRotatedDirichletRoots a n)^2 =
      (hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
        (realSobolevMiuraHillPotential a ha).property.1
        (realSobolevMiuraHillPotential a ha).property.2 n hn : ℂ) ∧
      miuraRotatedDirichletRoots a (-(n : ℤ)) = -miuraRotatedDirichletRoots a n ∧
      miuraRotatedDirichletRoots a 0 = 0 :=
  ⟨miuraRotatedDirichletRoots_sq a ha n hn,miuraRotatedDirichletRoots_neg_nat a ha n hn,
    miuraRotatedDirichletRoots_zero a ha⟩

theorem independent_Dirichlet_characteristic_entire_product
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j))) :
    TendstoLocallyUniformlyOn (fun N E => miuraHillDirichletPartialProduct a ha E N)
      (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)) atTop univ ∧
    TendstoLocallyUniformlyOn (fun N => deriv (fun E => miuraHillDirichletPartialProduct a ha E N))
      (deriv (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a))) atTop univ :=
  ⟨tendstoLocallyUniformlyOn_miuraHillDirichletPartialProduct a ha,
    tendstoLocallyUniformlyOn_deriv_miuraHillDirichletPartialProduct a ha⟩

theorem independent_Dirichlet_original_derivative_normalization
    (a : ScalarDomain 2) (ha : ∀ j, a.val j = conj (a.val (-j)))
    (n : ℕ) (hn : 1 ≤ n) :
    let q := realSobolevMiuraHillPotential a ha
    let E : ℂ := hillDirichletEnergy q.val q.property.1 q.property.2 n hn
    deriv (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a)))) (miuraRotatedDirichletRoots a n) =
        2*E*deriv (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)) E :=
  deriv_miura_rotated_Dirichlet_characteristic_at_root a ha n hn

end NLS.Articles.MKdVNLSHierarchies
