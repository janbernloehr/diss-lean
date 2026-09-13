import NLS.ZakharovShabat.PeriodicPolynomialCutoffIndependence
import NLS.ZakharovShabat.EntirePeriodicProductOrders
import NLS.ZakharovShabat.EntirePeriodicProductExistence

/-!
# Independence of the entire periodic product from spectral choices

Exact finite-cutoff identities preserve the normalization while the central
cluster grows. Uniqueness of limits then proves that the entire product is
independent of both the admissible central cutoff and the chosen pair labels.
-/

noncomputable section
open Filter Topology
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Enlarging an admissible central cutoff leaves the whole entire product unchanged. -/
theorem entirePeriodicProduct_eq_of_le (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N K : ℕ) (hNK : N ≤ K) (ξ η : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n)) :
    entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η =
      entirePeriodicProduct hp (weightedBaseToPair w φ) K ξ η := by
  funext z
  have he : (fun M => periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) N ξ η M z) =ᶠ[atTop]
      (fun M => periodicSpectralPolynomialCutoff hp (weightedBaseToPair w φ) K ξ η M z) := by
    filter_upwards [eventually_ge_atTop K] with M hM
    exact congrFun (periodicSpectralPolynomialCutoff_eq_of_le hp w φ N K M hNK hM ξ η hc hr) z
  exact tendsto_nhds_unique
    (((tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ N ξ η hξ hη).tendsto_at
      (Set.mem_univ z)).congr' he)
    ((tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ K ξ η hξ hη).tendsto_at (Set.mem_univ z))

/-- Any two admissible cutoffs and pair labelings define the same normalized entire function. -/
theorem entirePeriodicProduct_eq_of_choices (hp : p ≠ ⊤) (w : SpectralWeight)
    (φ : WeightedCoeffPair w.toWeight p) (N K : ℕ) (ξ η α β : ℤ → ℂ)
    (hξ : Memℓp (fun n => ξ n-(Real.pi : ℂ)*n) p)
    (hη : Memℓp (fun n => η n-(Real.pi : ℂ)*n) p)
    (hα : Memℓp (fun n => α n-(Real.pi : ℂ)*n) p)
    (hβ : Memℓp (fun n => β n-(Real.pi : ℂ)*n) p)
    (hc : PeriodicCountingData hp (weightedBaseToPair w φ) N)
    (hd : PeriodicCountingData hp (weightedBaseToPair w φ) K)
    (hr : ∀ n : ℤ, N < n.natAbs → PeriodicResonantPair hp w φ n (ξ n) (η n))
    (hs : ∀ n : ℤ, K < n.natAbs → PeriodicResonantPair hp w φ n (α n) (β n)) :
    entirePeriodicProduct hp (weightedBaseToPair w φ) N ξ η =
      entirePeriodicProduct hp (weightedBaseToPair w φ) K α β := by
  calc
    _ = entirePeriodicProduct hp (weightedBaseToPair w φ) (max N K) ξ η :=
      entirePeriodicProduct_eq_of_le hp w φ N _ (le_max_left _ _) ξ η hξ hη hc hr
    _ = entirePeriodicProduct hp (weightedBaseToPair w φ) (max N K) α β :=
      entirePeriodicProduct_eq_of_pairs hp w φ _ ξ η α β hξ hη hα hβ
        (fun n hn => hr n ((le_max_left N K).trans_lt hn))
        (fun n hn => hs n ((le_max_right N K).trans_lt hn))
    _ = entirePeriodicProduct hp (weightedBaseToPair w φ) K α β :=
      (entirePeriodicProduct_eq_of_le hp w φ K _ (le_max_right _ _) α β hα hβ hd hs).symm

/-- One entire function serves every larger cutoff on the common potential neighborhood.
It has the exact original zero orders and locally uniform polynomial and derivative limits. -/
theorem exists_uniform_cutoffIndependent_entirePeriodicProducts (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ U : Set (WeightedCoeffPair w.toWeight p),
      IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧ ∀ ψ ∈ U, ∃ ξ η : ℤ → ℂ, ∃ f : ℂ → ℂ,
        AnalyticOnNhd ℂ f Set.univ ∧
        (∀ z : ℂ, analyticOrderAt f z =
          (periodicAlgebraicMultiplicity hp (weightedBaseToPair w ψ) z : ℕ∞) ∧
          (f z = 0 ↔ z ∈ periodicSpectrum hp (weightedBaseToPair w ψ))) ∧
        ∀ N : ℕ, N₀ ≤ N →
          entirePeriodicProduct hp (weightedBaseToPair w ψ) N ξ η = f ∧
          TendstoLocallyUniformlyOn (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w ψ) N ξ η)
            f atTop Set.univ ∧
          TendstoLocallyUniformlyOn (fun M => deriv
            (periodicSpectralPolynomialCutoff hp (weightedBaseToPair w ψ) N ξ η M))
            (deriv f) atTop Set.univ := by
  obtain ⟨N₀,hN₀,U,ho,hconv,hφ,h0,hprod⟩ := exists_uniform_periodicSpectralProducts hp hp1 w φ
  refine ⟨N₀,hN₀,U,ho,hconv,hφ,h0,?_⟩
  intro ψ hψ
  obtain ⟨ξ,η,hξ,hη,hr,h⟩ := hprod ψ hψ
  have hc := (h N₀ le_rfl).1
  refine ⟨ξ,η,entirePeriodicProduct hp (weightedBaseToPair w ψ) N₀ ξ η,
    analyticOnNhd_entirePeriodicProduct hp _ N₀ ξ η hξ hη,?_,?_⟩
  · intro z
    exact ⟨analyticOrderAt_entirePeriodicProduct hp w ψ N₀ ξ η hξ hη hc hr z,
      entirePeriodicProduct_eq_zero_iff hp w ψ N₀ ξ η hξ hη hc hr z⟩
  · intro N hN
    have he := (entirePeriodicProduct_eq_of_le hp w ψ N₀ N hN ξ η hξ hη hc hr).symm
    refine ⟨he,?_,?_⟩
    · rw [← he]
      exact tendstoLocallyUniformlyOn_entirePeriodicProduct hp _ N ξ η hξ hη
    · rw [← he]
      exact tendstoLocallyUniformlyOn_deriv_entirePeriodicProduct hp _ N ξ η hξ hη

end NLS.ZakharovShabat
