import NLS.ZakharovShabat.ExponentInclusions
import NLS.ZakharovShabat.ParityFiniteApproximation

/-!
# Density of smaller-exponent potentials inside each parity

Every finite Fourier truncation has a coefficient-identical preimage at the
smaller exponent. Thus exponent inclusion has dense image inside either
parity subspace whenever the target exponent is finite.
-/

noncomputable section
open Set Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]

/-- Finite single coefficients are unchanged when their ambient exponent increases. -/
theorem exponentInclusion_single (h : p ≤ q) (n : ℤ) (c : ℂ) :
    Coeff.exponentInclusion h (lp.single p n c) = lp.single q n c := by
  ext k
  simp only [Coeff.exponentInclusion_apply, lp.single_apply]

/-- Any target truncation is the inclusion of a finite potential at the smaller exponent. -/
theorem exists_pairTruncate_preimage_exponent (h : p ≤ q) (φ : PairSpace q) (s : Finset ℤ) :
    ∃ ψ : PairSpace p, pairExponentInclusion h ψ = pairTruncate s φ := by
  refine ⟨(∑ n ∈ s, lp.single p n (φ.1 n), ∑ n ∈ s, lp.single p n (φ.2 n)), ?_⟩
  simp only [pairExponentInclusion_apply, map_sum, exponentInclusion_single, pairTruncate, Coeff.truncate]

/-- Smaller-exponent potentials are dense within either fixed parity of the finite target space. -/
theorem dense_pairExponentInclusion_parity (hq : q ≠ ⊤) (h : p ≤ q) (k : ℤ) :
    Dense {φ : pairParitySubspace (p := q) k | ∃ ψ : PairSpace p, pairExponentInclusion h ψ = φ.val} := by
  intro φ
  apply mem_closure_of_tendsto (tendsto_parityTruncate hq k φ)
  exact Eventually.of_forall (fun s => exists_pairTruncate_preimage_exponent h φ.val s)

end NLS.ZakharovShabat
