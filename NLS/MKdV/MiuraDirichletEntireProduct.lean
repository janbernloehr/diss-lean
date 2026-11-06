import NLS.MKdV.MiuraDirichletCharacteristicProduct
import NLS.ComplexAnalysis.SquaredCharacteristicLimit

/-! # Entire scalar Dirichlet products, including zero energy

The actual scalar characteristic and every spectral derivative are locally
uniform limits of the original positive-energy divisor products. No lower
bound away from zero energy is imposed on the evaluation set.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem tendstoLocallyUniformlyOn_miuraHillDirichletPartialProduct (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    TendstoLocallyUniformlyOn (fun N E => miuraHillDirichletPartialProduct a ha E N)
      (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)) atTop univ := by
  apply tendstoLocallyUniformlyOn_of_squared_characteristic
    (fun N z => boundaryCharacteristicPartialProduct (miuraRotatedDirichletRoots a) z N)
    (fun N E => miuraHillDirichletPartialProduct a ha E N)
    (fun z => z*hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2))
    (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a))
    (fun N => differentiableOn_univ.mp
      (analyticOnNhd_miuraHillDirichletPartialProduct a ha N).differentiableOn)
    (differentiableOn_univ.mp (analyticOnNhd_hillL2DirichletCharacteristic _).differentiableOn)
    (fun N z => boundaryCharacteristicPartialProduct_miura_eq a ha z N) (fun _ => rfl)
    (tendstoLocallyUniformlyOn_rotatedDirichletProduct a)

/-- The literal scalar product converges at every complex energy,
including the removable frequency zero and all divisor roots. -/
theorem tendsto_miuraHillDirichletPartialProduct (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (E : ℂ) :
    Tendsto (fun N => miuraHillDirichletPartialProduct a ha E N) atTop
      (𝓝 (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) E)) :=
  (tendstoLocallyUniformlyOn_miuraHillDirichletPartialProduct a ha).tendsto_at (mem_univ E)

theorem tendstoLocallyUniformlyOn_deriv_miuraHillDirichletPartialProduct (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) :
    TendstoLocallyUniformlyOn (fun N => deriv (fun E => miuraHillDirichletPartialProduct a ha E N))
      (deriv (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a))) atTop univ :=
  (tendstoLocallyUniformlyOn_miuraHillDirichletPartialProduct a ha).deriv
    (Filter.Eventually.of_forall (fun N =>
      (analyticOnNhd_miuraHillDirichletPartialProduct a ha N).differentiableOn)) isOpen_univ

end NLS.MKdV
