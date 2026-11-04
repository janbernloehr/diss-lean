import NLS.MKdV.MiuraDirichletEntireProduct
import NLS.KdV.HillFiniteAbelianPolynomials
import NLS.ComplexAnalysis.FiniteSpectralInterpolation

/-! # Cancellation of the actual common closed-gap product tail

Finite-gap scalar characteristics and Abelian numerators share every
sufficiently high factor. Cross multiplication of finite products, followed
by their checked limits, cancels this tail even at its zeros.
-/
noncomputable section
open Set Complex Filter Topology Polynomial
open NLS.ZakharovShabat NLS.KdV NLS.ComplexAnalysis
open scoped ENNReal ComplexConjugate
namespace NLS.MKdV

theorem freeHillValue_succ_complex (k : ℕ) :
    (freeHillValue (k+1 : ℕ) : ℂ) = ((Real.pi : ℂ)*(k+1))^2 := by
  simp only [freeHillValue,Int.cast_natCast]
  push_cast
  ring

def hillDirichletPrefixScale (K : ℕ) : ℂ :=
  ∏ k ∈ Finset.range K,-(freeHillValue (k+1 : ℕ) : ℂ)⁻¹

theorem hillDirichletPrefixScale_ne_zero (K : ℕ) : hillDirichletPrefixScale K ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro k _
  apply neg_ne_zero.mpr
  apply inv_ne_zero
  rw [freeHillValue_succ_complex]
  exact pow_ne_zero 2 (mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero)
    (by exact_mod_cast (show (k : ℝ)+1 ≠ 0 by positivity)))

theorem miuraHillDirichletPartialProduct_eq_gapRootFactors (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (E : ℂ) (N : ℕ) :
    miuraHillDirichletPartialProduct a ha E N =
      ∏ k ∈ Finset.range N,hillGapRootEnergyFactor
        (hillDirichletEnergies (realSobolevMiuraHillPotential a ha)) k E := by
  unfold miuraHillDirichletPartialProduct
  apply Finset.prod_congr rfl
  intro k _
  simp only [hillGapRootEnergyFactor,hillDirichletEnergies,freeHillValue_succ_complex]

theorem miuraHillDirichletPartialProduct_eq_nodal (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j))) (E : ℂ) (K : ℕ) :
    miuraHillDirichletPartialProduct a ha E K = hillDirichletPrefixScale K*
      (Lagrange.nodal (Finset.range K)
        (fun k => (hillDirichletEnergies (realSobolevMiuraHillPotential a ha) k : ℂ))).eval E := by
  rw [miuraHillDirichletPartialProduct_eq_gapRootFactors,Lagrange.eval_nodal]
  unfold hillDirichletPrefixScale
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  unfold hillGapRootEnergyFactor
  ring

theorem miuraAbelianNumerator_cross_dirichletPrefix (a : ScalarDomain 2)
    (ha : ∀ j, a.val j = conj (a.val (-j)))
    (σ : ℕ → ℝ) (hσ : σ ∈ hillGapRootBox (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2)
    (n K : ℕ) (hK : n ≤ K)
    (hclosed : ∀ k, K ≤ k → hillRealGapHalfLength (realSobolevMiuraHillPotential a ha).val
      (realSobolevMiuraHillPotential a ha).property.1 (realSobolevMiuraHillPotential a ha).property.2 (k+1) = 0)
    (E : ℂ) :
    hillAbelianNumeratorProduct σ n E*miuraHillDirichletPartialProduct a ha E K =
      (hillAbelianFiniteNumeratorPolynomial σ n K).eval E*
        hillL2DirichletCharacteristic (sobolevMiuraHillPotential a) E := by
  let q := realSobolevMiuraHillPotential a ha
  have hA := (multipliable_hillAbelianNumeratorFactors q.val q.property.1 q.property.2 σ hσ n E).hasProd.tendsto_prod_nat
  have hB := tendsto_miuraHillDirichletPartialProduct a ha E
  simp only [miuraHillDirichletPartialProduct_eq_gapRootFactors] at hB
  have htail (k : ℕ) (hk : K ≤ k) : hillAbelianNumeratorFactor σ n k E =
      hillGapRootEnergyFactor (hillDirichletEnergies q) k E := by
    have hroot := hillGapRoot_eq_Dirichlet_of_closed q σ hσ k (hclosed k hk)
    unfold hillAbelianNumeratorFactor
    rw [if_neg (by omega)]
    simp only [hillGapRootEnergyFactor,hillDirichletEnergies,hroot]
  have h := product_limits_cross_eq_of_tail_eq _ _ _ _ K hA hB htail
  simpa only [hillAbelianNumeratorProduct,← miuraHillDirichletPartialProduct_eq_gapRootFactors,
    ← eval_hillAbelianFiniteNumeratorPolynomial] using h

end NLS.MKdV
