import NLS.MKdV.MiuraDirichletRootIdentification

/-! # The actual scalar Dirichlet product on the full real Miura image

Pair the original signed roots before passing to the checked entire
characteristic limit. The resulting factors contain the independently
constructed scalar Dirichlet energies, with their original normalization.
-/
noncomputable section
open Set Complex Filter Topology NLS.ZakharovShabat NLS.KdV
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraHillDirichletPartialProduct (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (E : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N,
    ((hillDirichletEnergy (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1
      (realSobolevMiuraHillPotential a ha).property.2 (j+1) (by omega) : ℂ)-E)/
        ((Real.pi : ℂ)*(j+1))^2

theorem analyticOnNhd_miuraHillDirichletPartialProduct (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (N : ℕ) :
    AnalyticOnNhd ℂ (fun E => miuraHillDirichletPartialProduct a ha E N) univ := by
  intro E _
  unfold miuraHillDirichletPartialProduct
  apply Finset.analyticAt_fun_prod
  intro j _
  exact (analyticAt_const.sub analyticAt_id).div analyticAt_const
    (pow_ne_zero 2 (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) (by exact_mod_cast (show (j : ℝ)+1 ≠ 0 by positivity))))

theorem boundaryCharacteristicPartialProduct_miura_eq (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (z : ℂ) (N : ℕ) :
    boundaryCharacteristicPartialProduct (miuraRotatedDirichletRoots a) z N =
      z*miuraHillDirichletPartialProduct a ha (z^2) N := by
  rw [boundaryCharacteristicPartialProduct,prod_symmetric_interval]
  have hzero : singleSpectralFactor (miuraRotatedDirichletRoots a) z 0 = -z := by
    simp [singleSpectralFactor,singleSpectralDenominator,miuraRotatedDirichletRoots_zero a ha]
  rw [hzero,neg_mul,neg_neg]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  have hpos : (j : ℤ)+1 ≠ 0 := by omega
  have hneg : -((j : ℤ)+1) ≠ 0 := by omega
  have hpair := miuraRotatedDirichletRoots_neg_nat a ha (j+1) (by omega)
  have hsquare := miuraRotatedDirichletRoots_sq a ha (j+1) (by omega)
  simp only [Nat.cast_add,Nat.cast_one] at hpair hsquare
  unfold singleSpectralFactor singleSpectralDenominator
  rw [if_neg hpos,if_neg hneg,hpair]
  push_cast
  rw [← hsquare]
  field_simp
  ring

theorem tendstoLocallyUniformlyOn_rotatedDirichletProduct (a : ScalarDomain 2) :
    TendstoLocallyUniformlyOn
      (fun N z => boundaryCharacteristicPartialProduct (miuraRotatedDirichletRoots a) z N)
      (fun z => z*hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2)) atTop univ := by
  have ht := BoundaryCondition.tendstoLocallyUniformlyOn_canonicalProduct .dirichlet
    (by simp : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num)
    (periodOneBoundaryPotential (by simp) (by norm_num)
      (sourcePhase (sobolevSourceInclusion (a,a)))).val
    (periodOneBoundaryPotential (by simp) (by norm_num)
      (sourcePhase (sobolevSourceInclusion (a,a)))).property
  change TendstoLocallyUniformlyOn
    (fun N z => boundaryCharacteristicPartialProduct (miuraRotatedDirichletRoots a) z N)
    (periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a)))) atTop univ at ht
  have he : periodOneBoundaryCharacteristic (by simp) (by norm_num) .dirichlet
      (sourcePhase (sobolevSourceInclusion (a,a))) =
      (fun z => z*hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) (z^2)) :=
    funext (fun z => (miura_rotated_Dirichlet_characteristic a z).symm)
  rwa [he] at ht

/-- Every nonzero complex energy has the exact original scalar product. -/
theorem tendsto_miuraHillDirichletPartialProduct_of_ne_zero (a : ScalarDomain 2)
    (ha : ∀ n, a.val n = conj (a.val (-n))) (E : ℂ) (hE : E ≠ 0) :
    Tendsto (fun N => miuraHillDirichletPartialProduct a ha E N) atTop
      (𝓝 (hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) E)) := by
  let z := Complex.sqrt E
  have hz : z ≠ 0 := by
    intro he
    have hs := NLS.ComplexAnalysis.complex_sqrt_sq E
    change z^2 = E at hs
    rw [he,zero_pow (by norm_num)] at hs
    exact hE hs.symm
  have ht := ((tendstoLocallyUniformlyOn_rotatedDirichletProduct a).tendsto_at (mem_univ z)).const_mul z⁻¹
  simp only [boundaryCharacteristicPartialProduct_miura_eq a ha,← mul_assoc,inv_mul_cancel₀ hz,
    one_mul,NLS.ComplexAnalysis.complex_sqrt_sq,z] at ht
  exact ht

end NLS.MKdV
