import NLS.ZakharovShabat.UnweightedResonantDeterminant
import NLS.ZakharovShabat.ResonantDeterminantBounds
import NLS.ZakharovShabat.SymmetricEigenvalues

/-!
# Identifying scalar roots with the counted periodic eigenvalue pair

In a distant disc the original spectral algebraic count is two. Once a pair
exhausts the strip spectrum, positivity forces multiplicity one at each of two
distinct values, or multiplicity two at their common value. This identifies
the individual multiplicities without a general operator-valued argument principle.
-/

noncomputable section
open Complex Metric Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- A strip spectral pair inside the refined disc is exactly its enclosed spectrum. -/
theorem enclosedPeriodicSpectrum_eq_rootPair (hp : p ≠ ⊤) (φ : PairSpace p) (n : ℤ) (x y : ℂ)
    (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hs : ∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp φ ↔ z = x ∨ z = y) :
    enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4) = {x,y} := by
  classical
  ext z
  rw [mem_enclosedPeriodicSpectrum]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hz
    exact (hs z (refinedResonantDisk_subset_strip n hz.2)).mp hz.1
  · intro hz
    have hd : z ∈ refinedResonantDisk n := hz.elim (fun h => h ▸ hx) (fun h => h ▸ hy)
    exact ⟨(hs z (refinedResonantDisk_subset_strip n hd)).mpr hz,hd⟩

/-- Algebraic count two identifies the multiplicities of any exhaustive strip pair. -/
theorem periodicAlgebraicMultiplicity_eq_rootPair_count (hp : p ≠ ⊤) (φ : PairSpace p)
    (n : ℤ) (x y : ℂ) (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hs : ∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp φ ↔ z = x ∨ z = y)
    (hc : (∑ z ∈ enclosedPeriodicSpectrum hp φ ((Real.pi : ℂ)*n) (Real.pi/4),
      periodicAlgebraicMultiplicity hp φ z) = 2) :
    ∀ z ∈ resonantStrip n, periodicAlgebraicMultiplicity hp φ z = ({x,y} : Multiset ℂ).count z := by
  classical
  have hset := enclosedPeriodicSpectrum_eq_rootPair hp φ n x y hx hy hs
  rw [hset] at hc
  have hmx : 0 < periodicAlgebraicMultiplicity hp φ x :=
    (periodicAlgebraicMultiplicity_pos_iff hp φ x).mpr
      ((hs x (refinedResonantDisk_subset_strip n hx)).mpr (Or.inl rfl))
  have hmy : 0 < periodicAlgebraicMultiplicity hp φ y :=
    (periodicAlgebraicMultiplicity_pos_iff hp φ y).mpr
      ((hs y (refinedResonantDisk_subset_strip n hy)).mpr (Or.inr rfl))
  intro z hz
  by_cases hxy : x = y
  · subst y
    simp only [Finset.insert_eq_of_mem (Finset.mem_singleton_self x), Finset.sum_singleton] at hc
    by_cases hz' : z = x
    · subst z
      simpa using hc
    · have hm : periodicAlgebraicMultiplicity hp φ z = 0 := by
        by_contra h
        have hpz := (periodicAlgebraicMultiplicity_pos_iff hp φ z).mp (Nat.pos_of_ne_zero h)
        exact hz' (by simpa using (hs z hz).mp hpz)
      simp [hm, hz']
  · rw [Finset.sum_pair hxy] at hc
    have hx1 : periodicAlgebraicMultiplicity hp φ x = 1 := by omega
    have hy1 : periodicAlgebraicMultiplicity hp φ y = 1 := by omega
    by_cases hzx : z = x
    · subst z
      simp [hx1, hxy]
    · by_cases hzy : z = y
      · subst z
        simp [hy1, hxy, Ne.symm hxy]
      · have hm : periodicAlgebraicMultiplicity hp φ z = 0 := by
          by_contra h
          have hpz := (periodicAlgebraicMultiplicity_pos_iff hp φ z).mp (Nat.pos_of_ne_zero h)
          exact ((hs z hz).mp hpz).elim hzx hzy
        simp [hm, hzx, hzy]

/-- A scalar pair with its exact analytic orders agrees pointwise with spectral algebraic multiplicity. -/
theorem analyticOrderNatAt_eq_periodicAlgebraicMultiplicity_of_pair (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (n : ℤ) (x y : ℂ)
    (hx : x ∈ refinedResonantDisk n) (hy : y ∈ refinedResonantDisk n)
    (hs : ∀ z ∈ resonantStrip n, z ∈ periodicSpectrum hp (weightedBaseToPair w φ) ↔ z = x ∨ z = y)
    (hc : (∑ z ∈ enclosedPeriodicSpectrum hp (weightedBaseToPair w φ) ((Real.pi : ℂ)*n) (Real.pi/4),
      periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z) = 2)
    (ha : ∀ z ∈ resonantStrip n,
      analyticOrderNatAt (resonantDeterminantExtension hp w φ n) z = ({x,y} : Multiset ℂ).count z) :
    ∀ z ∈ resonantStrip n, analyticOrderNatAt (resonantDeterminantExtension hp w φ n) z =
      periodicAlgebraicMultiplicity hp (weightedBaseToPair w φ) z := by
  intro z hz
  exact (ha z hz).trans (periodicAlgebraicMultiplicity_eq_rootPair_count hp _ n x y hx hy hs hc z hz).symm

end NLS.ZakharovShabat
