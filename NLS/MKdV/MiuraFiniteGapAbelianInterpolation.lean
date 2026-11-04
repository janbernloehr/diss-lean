import NLS.MKdV.MiuraFiniteGapAbelianProducts
import NLS.KdV.HillDirichletSimplicity

/-! # Actual finite-gap Dirichlet interpolation of the normalized Hill numerator

The numerator is the independently normalized Abelian differential. Its
interpolation residues use the original scalar characteristic derivative.
Filled divided differences include all divisor terminals and zero energy.
-/
noncomputable section
open Set Complex Filter Topology Polynomial
open NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

def miuraFiniteAbelianInterpolationPolynomial (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) : Polynomial ℂ :=
  let q := realSobolevMiuraHillPotential a ha
  let σ := (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).val
  C ((2/((n : ℂ)*Real.pi))/
    hillAbelianCandidatePeriod q.val q.property.1 q.property.2 σ n n/hillDirichletPrefixScale K)*
      hillAbelianFiniteNumeratorPolynomial σ n K

theorem degree_miuraFiniteAbelianInterpolationPolynomial (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK : n ≤ K) :
    (miuraFiniteAbelianInterpolationPolynomial a ha n hn K).degree < K :=
  degree_const_mul_hillAbelianFiniteNumeratorPolynomial _ n K hn hK _

theorem miuraSelectedAbelianPsi_cross_nodal (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK : n ≤ K)
    (hclosed : ∀ k, K ≤ k → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (E : ℂ) :
    let q := realSobolevMiuraHillPotential a ha
    hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn E*
      (Lagrange.nodal (Finset.range K) (fun k => (hillDirichletEnergies q k : ℂ))).eval E =
        (miuraFiniteAbelianInterpolationPolynomial a ha n hn K).eval E*
          hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) E := by
  let q := realSobolevMiuraHillPotential a ha
  let σ := (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).val
  have hσ : σ ∈ hillGapRootBox q.val q.property.1 q.property.2 :=
    (hillAbelianSelectedGlobalRoots q.val q.property.1 q.property.2 n hn).property
  have he := miuraAbelianNumerator_cross_dirichletPrefix a ha σ hσ n K hK hclosed E
  rw [miuraHillDirichletPartialProduct_eq_nodal] at he
  have hD := hillDirichletPrefixScale_ne_zero K
  dsimp only [miuraFiniteAbelianInterpolationPolynomial,hillAbelianSelectedGlobalPsi,
    hillAbelianPsiCandidate]
  simp only [eval_mul,eval_C]
  exact normalize_characteristic_cross_identity _ _ _ _ _ _ _ hD he

/-- The original normalized differential has its actual finite Dirichlet
interpolation, with the original characteristic derivative at every node. -/
theorem miuraSelectedAbelianPsi_Dirichlet_interpolation (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK : n ≤ K)
    (hclosed : ∀ k, K ≤ k → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (E : ℂ) (hE : ∀ k ∈ Finset.range K,E ≠ (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k : ℂ)) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
    (∑ k ∈ Finset.range K,ψ (hillDirichletEnergies q k)*s E/
      (deriv s (hillDirichletEnergies q k)*(E-(hillDirichletEnergies q k : ℂ)))) = ψ E := by
  let q := realSobolevMiuraHillPotential a ha
  apply finite_characteristic_weighted_interpolation (Finset.range K)
    (fun k => (hillDirichletEnergies q k : ℂ)) (miuraFiniteAbelianInterpolationPolynomial a ha n hn K)
  · exact (injective_hillDirichletEnergies q).injOn
  · simpa only [Finset.card_range] using degree_miuraFiniteAbelianInterpolationPolynomial a ha n hn K hK
  · exact differentiableOn_univ.mp (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q.val q.property.1 q.property.2 n hn).differentiableOn
  · exact differentiableOn_univ.mp (analyticOnNhd_hillL2DirichletCharacteristic _).differentiableOn
  · exact miuraSelectedAbelianPsi_cross_nodal a ha n hn K hK hclosed
  · intro k _
    rw [← realSobolevMiuraHillPotential_toCoeff a ha]
    exact hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega)
  · intro k _
    rw [← realSobolevMiuraHillPotential_toCoeff a ha]
    exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 _
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega))
  · exact hE

/-- Filled interpolation at every complex energy, including all Dirichlet nodes. -/
theorem miuraSelectedAbelianPsi_Dirichlet_filled_interpolation (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (n : ℕ) (hn : 1 ≤ n) (K : ℕ) (hK : n ≤ K)
    (hclosed : ∀ k, K ≤ k → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (E : ℂ) :
    let q := realSobolevMiuraHillPotential a ha
    let ψ := hillAbelianSelectedGlobalPsi q.val q.property.1 q.property.2 n hn
    let s := hillL2DirichletCharacteristic (sobolevMiuraHillPotential a)
    (∑ k ∈ Finset.range K,ψ (hillDirichletEnergies q k)*
      dslope s (hillDirichletEnergies q k) E/deriv s (hillDirichletEnergies q k)) = ψ E := by
  let q := realSobolevMiuraHillPotential a ha
  apply finite_characteristic_dslope_interpolation (Finset.range K)
    (fun k => (hillDirichletEnergies q k : ℂ)) (miuraFiniteAbelianInterpolationPolynomial a ha n hn K)
  · exact (injective_hillDirichletEnergies q).injOn
  · simpa only [Finset.card_range] using degree_miuraFiniteAbelianInterpolationPolynomial a ha n hn K hK
  · exact differentiableOn_univ.mp (analyticOnNhd_hillAbelianSelectedGlobalPsi_energy q.val q.property.1 q.property.2 n hn).differentiableOn
  · exact differentiableOn_univ.mp (analyticOnNhd_hillL2DirichletCharacteristic _).differentiableOn
  · exact miuraSelectedAbelianPsi_cross_nodal a ha n hn K hK hclosed
  · intro k _
    rw [← realSobolevMiuraHillPotential_toCoeff a ha]
    exact hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega)
  · intro k _
    rw [← realSobolevMiuraHillPotential_toCoeff a ha]
    exact hillL2DirichletCharacteristic_deriv_ne_zero _ q.property.2 _
      (hillDirichletEnergy_zero q.val q.property.1 q.property.2 (k+1) (by omega))

end NLS.MKdV
