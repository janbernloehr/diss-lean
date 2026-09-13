import NLS.ZakharovShabat.EntirePeriodicProductZeros

/-!
# Entire products from actual periodic spectral data

The earlier displacement and counting results supply entire products for all
finite exponents strictly greater than one. A common potential neighborhood
and threshold support every larger central cutoff. Convergence and analyticity
are in the spectral parameter for each fixed potential.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Pair-label independence persists across the filled lattice by uniqueness of continuous extension. -/
theorem entirePeriodicProduct_eq_of_pairs (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N : ℕ) (ξ η α β : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hα : Memℓp (fun n => α n-(Real.pi : ℂ)*n) p)
    (hβ : Memℓp (fun n => β n-(Real.pi : ℂ)*n) p)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (hs : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (α n) (β n)) :
    entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η =
      entirePeriodicProduct hp (weightedBaseToPair w φ) N α β := by
  symm
  apply entirePeriodicProduct_unique hp _ N ξ η hξ hη _
    (continuousOn_univ.mp (analyticOnNhd_entirePeriodicProduct hp _ N α β hα hβ).continuousOn)
  intro z hz
  rw [entirePeriodicProduct_eq_offLattice hp _ N α β hα hβ z hz]
  exact (periodicSpectralProductOffLattice_eq_of_pairs N ξ η α β hr hs ⟨z,hz⟩).symm

/-- Every finite `p>1` potential has an entire full periodic product with exactly its actual spectral zeros.
The original polynomial cutoffs and their derivatives converge locally uniformly on the whole plane. -/
theorem exists_uniform_entirePeriodicProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ,
        ∀ N : ℕ, N₀ ≤ N →
          AnalyticOnNhd ℂ (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η) Set.univ ∧
          TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w ψ) N ξ η)
            (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η) atTop Set.univ ∧
          TendstoLocallyUniformlyOn (fun M => deriv
            (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w ψ) N ξ η M))
            (deriv (entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η)) atTop Set.univ ∧
          ∀ z : ℂ, entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η z = 0 ↔
            z ∈ periodicSpectrum hp (weightedBaseToPair w ψ) := by
  obtain ⟨N₀,hN₀,U,ho,hc,hφ,h0,hprod⟩ := exists_uniform_periodicSpectralProducts hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hc,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hξ,hη,hr,h⟩ := hprod ψ hψ
  refine ⟨ξ,η,fun N hN => ⟨analyticOnNhd_entirePeriodicProduct hp _ N ξ η hξ hη,
    tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ N ξ η hξ hη,
    tendstoLocallyUniformlyOn_deriv_entirePeriodicProduct hp _ N ξ η hξ hη,?_⟩⟩
  exact entirePeriodicProduct_eq_zero_iff hp w ψ N ξ η hξ hη (h N hN).1
    (fun n hn => hr n (by omega))

end NLS.ZakharovShabat
