import NLS.ZakharovShabat.ExponentBoundaryMultiplicity
import NLS.ZakharovShabat.CanonicalBoundaryRoots

/-!
# Canonical boundary coordinates across finite exponents
The central multisets retain their actual algebraic multiplicities under
coefficient inclusion. Comparing ordered enumerations in a sufficiently large
common block then identifies each signed coordinate, without identifying the
chosen cutoffs. The normalized characteristic is consequently unchanged.
-/

noncomputable section
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat.BoundaryCondition
variable {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] (b : BoundaryCondition)

/-- Central boundary spectra agree at every fixed cutoff across exponents. -/
theorem centralSpectrum_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) (N : ℕ) :
    b.centralSpectrum hp φ hφ N =
      b.centralSpectrum hq (pairExponentInclusion h φ) hψ N := by
  ext z
  rw [b.mem_centralSpectrum, b.mem_centralSpectrum, b.spectrum_exponent hp hq h φ hφ hψ]

/-- Central multisets, including all repetitions, agree across exponents. -/
theorem centralRoots_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (h : p ≤ q)
    (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) (N : ℕ) :
    b.centralRoots hp φ hφ N = b.centralRoots hq (pairExponentInclusion h φ) hψ N := by
  apply Multiset.ext.mpr
  intro z
  rw [b.count_centralRoots, b.count_centralRoots,
    b.centralSpectrum_exponent hp hq h φ hφ hψ,
    b.algebraicMultiplicity_exponent hp hq h φ hφ hψ]

/-- The canonical signed boundary coordinates are independent of the ambient finite exponent. -/
theorem canonicalRoots_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) :
    b.canonicalRoots hp hp1 φ hφ = b.canonicalRoots hq hq1 (pairExponentInclusion h φ) hψ := by
  obtain ⟨hξ, hsξ⟩ := b.canonicalRoots_spec hp hp1 φ hφ
  obtain ⟨hη, hsη⟩ := b.canonicalRoots_spec hq hq1 (pairExponentInclusion h φ) hψ
  funext n
  let K := max (max (b.canonicalRootCutoff hp hp1 φ hφ)
    (b.canonicalRootCutoff hq hq1 (pairExponentInclusion h φ) hψ)) n.natAbs
  have hpK : b.canonicalRootCutoff hp hp1 φ hφ ≤ K :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hqK : b.canonicalRootCutoff hq hq1 (pairExponentInclusion h φ) hψ ≤ K :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hnK : n.natAbs ≤ K := le_max_right _ _
  have he := (hξ.central_at_larger_cutoff K hpK).trans
    ((b.centralRoots_exponent hp hq h φ hφ hψ K).trans
      (hη.central_at_larger_cutoff K hqK).symm)
  exact NLS.ordered_finset_multiset_enumeration_unique complexLexLE
    (Finset.Icc (-(K : ℤ)) K) _ _ he
    (fun _ _ _ _ hij => hsξ hij) (fun _ _ _ _ hij => hsη hij)
    n (by simp only [Finset.mem_Icc]; omega)

/-- Canonical displacements commute with the coefficient-preserving inclusion. -/
theorem canonicalDisplacement_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) :
    Coeff.exponentInclusion h (b.canonicalDisplacement hp hp1 φ hφ) =
      b.canonicalDisplacement hq hq1 (pairExponentInclusion h φ) hψ := by
  ext n
  simp only [Coeff.exponentInclusion_apply, canonicalDisplacement_apply,
    b.canonicalRoots_exponent hp hq hp1 hq1 h φ hφ hψ]

/-- The intrinsic normalized boundary characteristic is independent of the finite exponent. -/
theorem characteristic_exponent (hp : p ≠ ⊤) (hq : q ≠ ⊤) (hp1 : 1 < p)
    (hq1 : 1 < q) (h : p ≤ q) (φ : PairSpace p) (hφ : φ ∈ dirichletSubspace)
    (hψ : pairExponentInclusion h φ ∈ dirichletSubspace) :
    b.characteristic hp φ hφ = b.characteristic hq (pairExponentInclusion h φ) hψ := by
  rw [b.characteristic_eq_canonicalProduct hp hp1, b.characteristic_eq_canonicalProduct hq hq1,
    b.canonicalRoots_exponent hp hq hp1 hq1 h φ hφ hψ]

end NLS.ZakharovShabat.BoundaryCondition
