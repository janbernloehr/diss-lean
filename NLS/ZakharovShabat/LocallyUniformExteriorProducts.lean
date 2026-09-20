import NLS.ZakharovShabat.UniformExteriorDisplacements
import NLS.ZakharovShabat.RelativeProductErrorBounds
import NLS.ZakharovShabat.CanonicalParityProducts
import NLS.Fourier.IntervalKernel

/-!
# Exterior product estimates uniform near a potential

For each tolerance there is one open convex potential neighborhood and one
spectral threshold controlling all three canonical/free ratios. The same
neighborhood includes zero. The tolerance is chosen before the neighborhood.
-/

noncomputable section
open Set Complex Filter Topology NLS.Fourier
open scoped ENNReal
namespace NLS.ZakharovShabat
variable {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- All canonical ratios have a common locally uniform exterior estimate in weighted potential spaces. -/
theorem exists_uniform_exterior_canonicalProducts_weighted (hp : p ≠ ⊤) (hp1 : 1 < p)
    (w : SpectralWeight) (φ : WeightedCoeffPair w.toWeight p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (WeightedCoeffPair w.toWeight p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, ∀ ψ ∈ U, weightedBaseToPair w ψ ∈ pairParitySubspace 0 →
        ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
          ‖canonicalPeriodicProduct hp (weightedBaseToPair w ψ) z/((freeDiscriminant z)^2-4)-1‖ ≤ ε ∧
          ‖canonicalParityProduct hp (weightedBaseToPair w ψ) 0 z/(freeDiscriminant z-2)-1‖ ≤ ε ∧
          ‖canonicalParityProduct hp (weightedBaseToPair w ψ) 1 z/(freeDiscriminant z+2)-1‖ ≤ ε := by
  let δ := Real.log (1+ε)/2
  have hδ : 0 < δ := div_pos (Real.log_pos (by linarith)) (by norm_num)
  have he : Real.exp (2*δ)-1 = ε := by
    rw [show 2*δ = Real.log (1+ε) by dsimp [δ]; ring, Real.exp_log (by linarith)]
    ring
  obtain ⟨N, _, U, ho, hconv, hφ, h0, R, hdata⟩ :=
    exists_uniform_small_exteriorDisplacements hp hp1 w φ hr hrπ hδ
  refine ⟨U, ho, hconv, hφ, h0, R, ?_⟩
  intro ψ hψ heven z hz hsep
  obtain ⟨ξ, η, h, hb⟩ := hdata ψ hψ heven
  have ht := norm_spectralProducts_div_free_sub_one_le hp ξ η h.left_displacement h.right_displacement
    z hr hsep hδ.le (hb z hz hsep).1 (hb z hz hsep).2
  rw [h.fullProduct_eq_canonical, ← (h.canonicalParity_eq_products hp1).1,
    ← (h.canonicalParity_eq_products hp1).2, he] at ht
  exact ht

/-- The three exterior estimates hold on one open convex neighborhood in the original pair space. -/
theorem exists_uniform_exterior_canonicalProducts (hp : p ≠ ⊤) (hp1 : 1 < p) (φ : PairSpace p)
    {r : ℝ} (hr : 0 < r) (hrπ : r ≤ Real.pi/4) {ε : ℝ} (hε : 0 < ε) :
    ∃ U : Set (PairSpace p), IsOpen U ∧ Convex ℝ U ∧ φ ∈ U ∧ 0 ∈ U ∧
      ∃ R : ℝ, ∀ ψ ∈ U, ψ ∈ pairParitySubspace 0 →
        ∀ z : ℂ, R ≤ ‖z‖ → (∀ n : ℤ, r ≤ ‖z-(Real.pi : ℂ)*n‖) →
          ‖canonicalPeriodicProduct hp ψ z/((freeDiscriminant z)^2-4)-1‖ ≤ ε ∧
          ‖canonicalParityProduct hp ψ 0 z/(freeDiscriminant z-2)-1‖ ≤ ε ∧
          ‖canonicalParityProduct hp ψ 1 z/(freeDiscriminant z+2)-1‖ ≤ ε := by
  obtain ⟨U, ho, hconv, hφ, h0, R, hdata⟩ := exists_uniform_exterior_canonicalProducts_weighted hp hp1
    SpectralWeight.one (unitBaseEquiv.symm φ) hr hrπ hε
  have he (ψ : PairSpace p) : weightedBaseToPair SpectralWeight.one (unitBaseEquiv.symm ψ) = ψ := by
    rw [← unitBaseEquiv_eq, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨unitBaseEquiv.symm ⁻¹' U, ho.preimage unitBaseEquiv.symm.continuous,
    hconv.linear_preimage (unitBaseEquiv.symm.toContinuousLinearMap.restrictScalars ℝ).toLinearMap,
    hφ, by simpa only [mem_preimage, map_zero] using h0, R, ?_⟩
  intro ψ hψ heven z hz hsep
  simpa only [he] using hdata (unitBaseEquiv.symm ψ) hψ (by rw [he]; exact heven) z hz hsep

end NLS.ZakharovShabat
