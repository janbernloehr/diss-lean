import NLS.ZakharovShabat.CanonicalPeriodicEndpoints
import NLS.SequenceSpaces.OrderedPairedUnique

/-! # Canonical periodic endpoints from intrinsic spectral data

The signed indexing of complete ordered endpoint sequences is determined by
the original periodic spectrum together with actual algebraic multiplicities.
The two potentials may differ; both central multisets and every distant pair
are compared directly, so no phase-dependent labeling choice is assumed.
-/

noncomputable section
open Set
open NLS.ComplexAnalysis
open scoped ENNReal Classical
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Central root multisets agree when the intrinsic spectrum and multiplicity agree. -/
theorem centralPeriodicRoots_eq_of_spectral_data (hp : p ≠ ⊤) (φ ψ : PairSpace p)
    (hspec : periodicSpectrum hp φ = periodicSpectrum hp ψ)
    (hmult : ∀ z, periodicAlgebraicMultiplicity hp φ z =
      periodicAlgebraicMultiplicity hp ψ z) (K : ℕ) :
    centralPeriodicRoots hp φ K = centralPeriodicRoots hp ψ K := by
  have hc : centralPeriodicSpectrum hp φ K = centralPeriodicSpectrum hp ψ K := by
    ext z
    simp only [mem_centralPeriodicSpectrum]
    rw [hspec]
  apply Multiset.ext.mpr
  intro z
  rw [count_centralPeriodicRoots, count_centralPeriodicRoots, hc, hmult z]

/-- The two-root multiset in a distant disc is intrinsic spectral data. -/
theorem PeriodicEndpointPair.multiset_eq_of_spectral_data {hp : p ≠ ⊤}
    {φ ψ : PairSpace p} {n : ℤ} {x y a b : ℂ}
    (h : PeriodicEndpointPair hp φ n x y)
    (h' : PeriodicEndpointPair hp ψ n a b)
    (hspec : periodicSpectrum hp φ = periodicSpectrum hp ψ)
    (hmult : ∀ z, periodicAlgebraicMultiplicity hp φ z =
      periodicAlgebraicMultiplicity hp ψ z) :
    ({x,y} : Multiset ℂ) = {a,b} := by
  have hd : enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4) =
      enclosedPeriodicSpectrum hp ψ ((Real.pi : ℂ)*n) (Real.pi/4) := by
    ext z
    simp only [mem_enclosedPeriodicSpectrum]
    rw [hspec]
  calc
    ({x,y} : Multiset ℂ) =
        ∑ z ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4),
          Multiset.replicate (periodicAlgebraicMultiplicity hp φ z) z := h.multiset_eq_roots
    _ = ∑ z ∈ enclosedPeriodicSpectrum hp ψ ((Real.pi : ℂ)*n) (Real.pi/4),
          Multiset.replicate (periodicAlgebraicMultiplicity hp ψ z) z := by
      rw [hd]
      apply Finset.sum_congr rfl
      intro z _
      rw [hmult z]
    _ = {a,b} := h'.multiset_eq_roots.symm

/-- Ordered signed endpoints depend only on the periodic spectrum and its multiplicities. -/
theorem canonicalPeriodicEndpoints_eq_of_spectral_data (hp : p ≠ ⊤) (hp1 : 1 < p)
    (φ ψ : PairSpace p) (hφ : φ ∈ pairParitySubspace 0)
    (hψ : ψ ∈ pairParitySubspace 0)
    (hspec : periodicSpectrum hp φ = periodicSpectrum hp ψ)
    (hmult : ∀ z, periodicAlgebraicMultiplicity hp φ z =
      periodicAlgebraicMultiplicity hp ψ z) :
    canonicalPeriodicLeft hp hp1 φ hφ = canonicalPeriodicLeft hp hp1 ψ hψ ∧
      canonicalPeriodicRight hp hp1 φ hφ = canonicalPeriodicRight hp hp1 ψ hψ := by
  let ξ := canonicalPeriodicLeft hp hp1 φ hφ
  let η := canonicalPeriodicRight hp hp1 φ hφ
  let a := canonicalPeriodicLeft hp hp1 ψ hψ
  let b := canonicalPeriodicRight hp hp1 ψ hψ
  let N := canonicalPeriodicCutoff hp hp1 φ hφ
  let M := canonicalPeriodicCutoff hp hp1 ψ hψ
  let K := max N M
  have hφspec := canonicalPeriodicEndpoints_spec hp hp1 φ hφ
  have hψspec := canonicalPeriodicEndpoints_spec hp hp1 ψ hψ
  have hcφ := hφspec.1.central_at_larger_cutoff K (le_max_left N M)
  have hcψ := hψspec.1.central_at_larger_cutoff K (le_max_right N M)
  have hroots :
      (∑ n ∈ Finset.Icc (-(K : ℤ)) K, ({ξ n,η n} : Multiset ℂ)) =
        ∑ n ∈ Finset.Icc (-(K : ℤ)) K, ({a n,b n} : Multiset ℂ) :=
    hcφ.roots.trans ((centralPeriodicRoots_eq_of_spectral_data hp φ ψ hspec hmult K).trans hcψ.roots.symm)
  have hcenter := NLS.ordered_paired_multiset_enumeration_unique complexLexLE
    (Finset.Icc (-(K : ℤ)) K) ξ η a b hroots
    (fun n _ => hφspec.2.1 n) (fun i _ j _ hij => hφspec.2.2 i j hij)
    (fun n _ => hψspec.2.1 n) (fun i _ j _ hij => hψspec.2.2 i j hij)
  have he (n : ℤ) : ξ n = a n ∧ η n = b n := by
    by_cases hn : n.natAbs ≤ K
    · apply hcenter n
      simp only [Finset.mem_Icc]
      omega
    · have hpair := (hφspec.1.distant n (by omega)).multiset_eq_of_spectral_data
        (hψspec.1.distant n (by omega)) hspec hmult
      exact NLS.ordered_pair_unique complexLexLE (ξ n) (η n) (a n) (b n) hpair
        (hφspec.2.1 n) (hψspec.2.1 n)
  exact ⟨funext (fun n => (he n).1), funext (fun n => (he n).2)⟩

end NLS.ZakharovShabat
