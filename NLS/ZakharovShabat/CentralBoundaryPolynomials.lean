import NLS.ZakharovShabat.BoundaryRootCutoffGrowth
import NLS.ZakharovShabat.BoundaryCharacteristicProducts

/-!
# Intrinsic central boundary polynomials
The finite polynomial uses the actual central spectrum and its original
algebraic multiplicities. Every complete labeling gives the same normalized
cutoff once the entire initial central block is included.
-/

noncomputable section
open Set
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace BoundaryCondition

/-- The central root polynomial, defined from the restricted operator alone. -/
def centralPolynomial (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ ζ ∈ b.centralSpectrum hp φ hφ N, (ζ-z)^(b.algebraicMultiplicity hp φ hφ ζ)

/-- The central polynomial with the literal Section 9 normalization. -/
def normalizedCentralPolynomial (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ) : ℂ :=
  -b.centralPolynomial hp φ hφ N z / ∏ n ∈ Finset.Icc (-(N : ℤ)) N, singleSpectralDenominator n

/-- Multiplying the central root multiset reproduces the intrinsic polynomial. -/
theorem prod_centralRoots (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) (z : ℂ) :
    ((b.centralRoots hp φ hφ N).map (fun ζ => ζ-z)).prod = b.centralPolynomial hp φ hφ N z := by
  rw [Finset.prod_multiset_map_count]
  have hs : (b.centralRoots hp φ hφ N).toFinset = b.centralSpectrum hp φ hφ N := by
    ext ζ
    simp only [Multiset.mem_toFinset,b.mem_centralRoots]
  rw [hs]
  apply Finset.prod_congr rfl
  intro ζ hζ
  rw [b.count_centralRoots,if_pos hζ]

/-- Every central boundary polynomial is entire, without a counting hypothesis. -/
theorem analyticOnNhd_centralPolynomial (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) : AnalyticOnNhd ℂ (b.centralPolynomial hp φ hφ N) univ := by
  intro z _
  unfold centralPolynomial
  fun_prop

/-- The normalized intrinsic approximants are entire at every cutoff. -/
theorem analyticOnNhd_normalizedCentralPolynomial (b : BoundaryCondition) (hp : p ≠ ⊤) (φ : PairSpace p)
    (hφ : φ ∈ dirichletSubspace) (N : ℕ) :
    AnalyticOnNhd ℂ (b.normalizedCentralPolynomial hp φ hφ N) univ := by
  intro z _
  unfold normalizedCentralPolynomial centralPolynomial
  fun_prop

end BoundaryCondition

/-- Every sufficiently large full boundary cutoff is the normalized intrinsic central polynomial. -/
theorem BoundaryRootLabeling.cutoff_eq_normalizedCentral {b : BoundaryCondition} {hp : p ≠ ⊤}
    {φ : PairSpace p} {hφ : φ ∈ dirichletSubspace} {N : ℕ} {ξ : ℤ → ℂ}
    (h : BoundaryRootLabeling b hp φ hφ N ξ) (K : ℕ) (hK : N ≤ K) (z : ℂ) :
    boundaryCharacteristicPartialProduct ξ z K = b.normalizedCentralPolynomial hp φ hφ K z := by
  have hm := b.prod_centralRoots hp φ hφ K z
  rw [← h.central_at_larger_cutoff K hK] at hm
  have he (s : Finset ℤ) : ((∑ n ∈ s, ({ξ n} : Multiset ℂ)).map (fun ζ => ζ-z)).prod =
      ∏ n ∈ s, (ξ n-z) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert n s hn ih =>
      rw [Finset.sum_insert hn,Multiset.map_add,Multiset.prod_add,ih,Finset.prod_insert hn]
      simp only [Multiset.map_singleton,Multiset.prod_singleton]
  rw [he] at hm
  simp only [boundaryCharacteristicPartialProduct,singleSpectralFactor,Finset.prod_div_distrib,
    hm,BoundaryCondition.normalizedCentralPolynomial,neg_div]

end NLS.ZakharovShabat
